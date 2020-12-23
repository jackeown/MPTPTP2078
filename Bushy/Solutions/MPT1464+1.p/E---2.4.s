%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : filter_1__t59_filter_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:10 EDT 2019

% Result     : Theorem 230.70s
% Output     : CNFRefutation 230.70s
% Verified   : 
% Statistics : Number of formulae       :  118 (1220 expanded)
%              Number of clauses        :   91 ( 383 expanded)
%              Number of leaves         :   13 ( 301 expanded)
%              Depth                    :   31
%              Number of atoms          : 1047 (14900 expanded)
%              Number of equality atoms :    3 (  18 expanded)
%              Maximal formula depth    :   35 (   8 average)
%              Maximal clause size      :  196 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t59_filter_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v3_filter_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v19_lattices(X2,X1)
            & v20_lattices(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X1))
                         => ( ( r2_hidden(k7_filter_0(X1,X3,X4),X2)
                              & r2_hidden(k7_filter_0(X1,X5,X6),X2) )
                           => ( r2_hidden(k7_filter_0(X1,k3_lattices(X1,X3,X5),k3_lattices(X1,X4,X6)),X2)
                              & r2_hidden(k7_filter_0(X1,k4_lattices(X1,X3,X5),k4_lattices(X1,X4,X6)),X2) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',t59_filter_1)).

fof(t8_filter_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( ( ~ v1_xboole_0(X2)
              & v19_lattices(X2,X1)
              & v20_lattices(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2) )
                    <=> r2_hidden(k4_lattices(X1,X3,X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',t8_filter_0)).

fof(d11_filter_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k7_filter_0(X1,X2,X3) = k4_lattices(X1,k4_filter_0(X1,X2,X3),k4_filter_0(X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',d11_filter_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',t4_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',t7_boole)).

fof(l68_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v3_filter_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v19_lattices(X2,X1)
            & v20_lattices(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ( ( r2_hidden(k4_filter_0(X1,X3,X4),X2)
                          & r2_hidden(k4_filter_0(X1,X5,X4),X2) )
                       => r2_hidden(k4_filter_0(X1,k3_lattices(X1,X3,X5),X4),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',l68_filter_1)).

fof(l66_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v3_filter_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v19_lattices(X2,X1)
            & v20_lattices(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ( r2_hidden(k4_filter_0(X1,X3,X4),X2)
                       => ( r2_hidden(k4_filter_0(X1,X3,k3_lattices(X1,X4,X5)),X2)
                          & r2_hidden(k4_filter_0(X1,X3,k3_lattices(X1,X5,X4)),X2)
                          & r2_hidden(k4_filter_0(X1,k4_lattices(X1,X3,X5),X4),X2)
                          & r2_hidden(k4_filter_0(X1,k4_lattices(X1,X5,X3),X4),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',l66_filter_1)).

fof(dt_k3_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v4_lattices(X1)
        & l2_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k3_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',dt_k3_lattices)).

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
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',cc1_lattices)).

fof(dt_l3_lattices,axiom,(
    ! [X1] :
      ( l3_lattices(X1)
     => ( l1_lattices(X1)
        & l2_lattices(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',dt_l3_lattices)).

fof(l70_filter_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & v3_filter_0(X1)
        & l3_lattices(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v19_lattices(X2,X1)
            & v20_lattices(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ( ( r2_hidden(k4_filter_0(X1,X3,X4),X2)
                          & r2_hidden(k4_filter_0(X1,X3,X5),X2) )
                       => r2_hidden(k4_filter_0(X1,X3,k4_lattices(X1,X4,X5)),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',l70_filter_1)).

fof(dt_k4_filter_0,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v10_lattices(X1)
        & l3_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',dt_k4_filter_0)).

fof(dt_k4_lattices,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v6_lattices(X1)
        & l1_lattices(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/filter_1__t59_filter_1.p',dt_k4_lattices)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v10_lattices(X1)
          & v3_filter_0(X1)
          & l3_lattices(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v19_lattices(X2,X1)
              & v20_lattices(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X1))
                           => ( ( r2_hidden(k7_filter_0(X1,X3,X4),X2)
                                & r2_hidden(k7_filter_0(X1,X5,X6),X2) )
                             => ( r2_hidden(k7_filter_0(X1,k3_lattices(X1,X3,X5),k3_lattices(X1,X4,X6)),X2)
                                & r2_hidden(k7_filter_0(X1,k4_lattices(X1,X3,X5),k4_lattices(X1,X4,X6)),X2) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t59_filter_1])).

fof(c_0_14,plain,(
    ! [X100,X101,X102,X103] :
      ( ( ~ r2_hidden(X102,X101)
        | ~ r2_hidden(X103,X101)
        | r2_hidden(k4_lattices(X100,X102,X103),X101)
        | ~ m1_subset_1(X103,u1_struct_0(X100))
        | ~ m1_subset_1(X102,u1_struct_0(X100))
        | v1_xboole_0(X101)
        | ~ v19_lattices(X101,X100)
        | ~ v20_lattices(X101,X100)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( r2_hidden(X102,X101)
        | ~ r2_hidden(k4_lattices(X100,X102,X103),X101)
        | ~ m1_subset_1(X103,u1_struct_0(X100))
        | ~ m1_subset_1(X102,u1_struct_0(X100))
        | v1_xboole_0(X101)
        | ~ v19_lattices(X101,X100)
        | ~ v20_lattices(X101,X100)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( r2_hidden(X103,X101)
        | ~ r2_hidden(k4_lattices(X100,X102,X103),X101)
        | ~ m1_subset_1(X103,u1_struct_0(X100))
        | ~ m1_subset_1(X102,u1_struct_0(X100))
        | v1_xboole_0(X101)
        | ~ v19_lattices(X101,X100)
        | ~ v20_lattices(X101,X100)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( ~ v1_xboole_0(X101)
        | m1_subset_1(esk12_2(X100,X101),u1_struct_0(X100))
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( v19_lattices(X101,X100)
        | m1_subset_1(esk12_2(X100,X101),u1_struct_0(X100))
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( v20_lattices(X101,X100)
        | m1_subset_1(esk12_2(X100,X101),u1_struct_0(X100))
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | m1_subset_1(esk12_2(X100,X101),u1_struct_0(X100))
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( ~ v1_xboole_0(X101)
        | m1_subset_1(esk13_2(X100,X101),u1_struct_0(X100))
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( v19_lattices(X101,X100)
        | m1_subset_1(esk13_2(X100,X101),u1_struct_0(X100))
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( v20_lattices(X101,X100)
        | m1_subset_1(esk13_2(X100,X101),u1_struct_0(X100))
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | m1_subset_1(esk13_2(X100,X101),u1_struct_0(X100))
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( ~ v1_xboole_0(X101)
        | ~ r2_hidden(esk12_2(X100,X101),X101)
        | ~ r2_hidden(esk13_2(X100,X101),X101)
        | ~ r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( v19_lattices(X101,X100)
        | ~ r2_hidden(esk12_2(X100,X101),X101)
        | ~ r2_hidden(esk13_2(X100,X101),X101)
        | ~ r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( v20_lattices(X101,X100)
        | ~ r2_hidden(esk12_2(X100,X101),X101)
        | ~ r2_hidden(esk13_2(X100,X101),X101)
        | ~ r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | ~ r2_hidden(esk12_2(X100,X101),X101)
        | ~ r2_hidden(esk13_2(X100,X101),X101)
        | ~ r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( ~ v1_xboole_0(X101)
        | r2_hidden(esk12_2(X100,X101),X101)
        | r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( v19_lattices(X101,X100)
        | r2_hidden(esk12_2(X100,X101),X101)
        | r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( v20_lattices(X101,X100)
        | r2_hidden(esk12_2(X100,X101),X101)
        | r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | r2_hidden(esk12_2(X100,X101),X101)
        | r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( ~ v1_xboole_0(X101)
        | r2_hidden(esk13_2(X100,X101),X101)
        | r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( v19_lattices(X101,X100)
        | r2_hidden(esk13_2(X100,X101),X101)
        | r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( v20_lattices(X101,X100)
        | r2_hidden(esk13_2(X100,X101),X101)
        | r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) )
      & ( m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | r2_hidden(esk13_2(X100,X101),X101)
        | r2_hidden(k4_lattices(X100,esk12_2(X100,X101),esk13_2(X100,X101)),X101)
        | v1_xboole_0(X101)
        | ~ m1_subset_1(X101,k1_zfmisc_1(u1_struct_0(X100)))
        | v2_struct_0(X100)
        | ~ v10_lattices(X100)
        | ~ l3_lattices(X100) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_filter_0])])])])])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v10_lattices(esk1_0)
    & v3_filter_0(esk1_0)
    & l3_lattices(esk1_0)
    & ~ v1_xboole_0(esk2_0)
    & v19_lattices(esk2_0,esk1_0)
    & v20_lattices(esk2_0,esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk1_0))
    & r2_hidden(k7_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    & r2_hidden(k7_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    & ( ~ r2_hidden(k7_filter_0(esk1_0,k3_lattices(esk1_0,esk3_0,esk5_0),k3_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
      | ~ r2_hidden(k7_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),esk2_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ v10_lattices(X22)
      | ~ l3_lattices(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_subset_1(X24,u1_struct_0(X22))
      | k7_filter_0(X22,X23,X24) = k4_lattices(X22,k4_filter_0(X22,X23,X24),k4_filter_0(X22,X24,X23)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d11_filter_0])])])])).

cnf(c_0_17,plain,
    ( r2_hidden(k4_lattices(X4,X1,X3),X2)
    | v1_xboole_0(X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | ~ v19_lattices(X2,X4)
    | ~ v20_lattices(X2,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v10_lattices(X4)
    | ~ l3_lattices(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X89,X90,X91] :
      ( ~ r2_hidden(X89,X90)
      | ~ m1_subset_1(X90,k1_zfmisc_1(X91))
      | m1_subset_1(X89,X91) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_19,plain,(
    ! [X96,X97] :
      ( ~ r2_hidden(X96,X97)
      | ~ v1_xboole_0(X97) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_20,negated_conjecture,
    ( ~ r2_hidden(k7_filter_0(esk1_0,k3_lattices(esk1_0,esk3_0,esk5_0),k3_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ r2_hidden(k7_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,plain,
    ( v2_struct_0(X1)
    | k7_filter_0(X1,X2,X3) = k4_lattices(X1,k4_filter_0(X1,X2,X3),k4_filter_0(X1,X3,X2))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( l3_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,negated_conjecture,
    ( v10_lattices(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( v2_struct_0(X4)
    | v1_xboole_0(X2)
    | r2_hidden(k4_lattices(X4,X1,X3),X2)
    | ~ v10_lattices(X4)
    | ~ l3_lattices(X4)
    | ~ v19_lattices(X2,X4)
    | ~ v20_lattices(X2,X4)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X1,u1_struct_0(X4))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4))) ),
    inference(cn,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X63,X64,X65,X66,X67] :
      ( v2_struct_0(X63)
      | ~ v10_lattices(X63)
      | ~ v3_filter_0(X63)
      | ~ l3_lattices(X63)
      | v1_xboole_0(X64)
      | ~ v19_lattices(X64,X63)
      | ~ v20_lattices(X64,X63)
      | ~ m1_subset_1(X64,k1_zfmisc_1(u1_struct_0(X63)))
      | ~ m1_subset_1(X65,u1_struct_0(X63))
      | ~ m1_subset_1(X66,u1_struct_0(X63))
      | ~ m1_subset_1(X67,u1_struct_0(X63))
      | ~ r2_hidden(k4_filter_0(X63,X65,X66),X64)
      | ~ r2_hidden(k4_filter_0(X63,X67,X66),X64)
      | r2_hidden(k4_filter_0(X63,k3_lattices(X63,X65,X67),X66),X64) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l68_filter_1])])])])).

cnf(c_0_29,negated_conjecture,
    ( ~ r2_hidden(k4_lattices(esk1_0,k4_filter_0(esk1_0,k3_lattices(esk1_0,esk3_0,esk5_0),k3_lattices(esk1_0,esk4_0,esk6_0)),k4_filter_0(esk1_0,k3_lattices(esk1_0,esk4_0,esk6_0),k3_lattices(esk1_0,esk3_0,esk5_0))),esk2_0)
    | ~ r2_hidden(k7_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_lattices(X1,X2,X3),X4)
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,X4)
    | ~ r2_hidden(X2,X4)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v20_lattices(X4,X1)
    | ~ v19_lattices(X4,X1)
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[c_0_25,c_0_26]),c_0_26]),c_0_27])).

cnf(c_0_31,negated_conjecture,
    ( v20_lattices(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_33,negated_conjecture,
    ( v19_lattices(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k4_filter_0(X1,k3_lattices(X1,X3,X5),X4),X2)
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ l3_lattices(X1)
    | ~ v19_lattices(X2,X1)
    | ~ v20_lattices(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r2_hidden(k4_filter_0(X1,X3,X4),X2)
    | ~ r2_hidden(k4_filter_0(X1,X5,X4),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(k4_lattices(esk1_0,k4_filter_0(esk1_0,k3_lattices(esk1_0,esk3_0,esk5_0),k3_lattices(esk1_0,esk4_0,esk6_0)),k4_filter_0(esk1_0,k3_lattices(esk1_0,esk4_0,esk6_0),k3_lattices(esk1_0,esk3_0,esk5_0))),esk2_0)
    | ~ r2_hidden(k4_lattices(esk1_0,k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),k4_filter_0(esk1_0,k4_lattices(esk1_0,esk4_0,esk6_0),k4_lattices(esk1_0,esk3_0,esk5_0))),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k4_lattices(esk1_0,X1,X2),esk2_0)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_37,plain,
    ( r2_hidden(k4_filter_0(X1,k3_lattices(X1,X2,X3),X4),X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k4_filter_0(X1,X3,X4),X5)
    | ~ r2_hidden(k4_filter_0(X1,X2,X4),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v20_lattices(X5,X1)
    | ~ v19_lattices(X5,X1)
    | ~ l3_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_34,c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v3_filter_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_39,plain,(
    ! [X58,X59,X60,X61,X62] :
      ( ( r2_hidden(k4_filter_0(X58,X60,k3_lattices(X58,X61,X62)),X59)
        | ~ r2_hidden(k4_filter_0(X58,X60,X61),X59)
        | ~ m1_subset_1(X62,u1_struct_0(X58))
        | ~ m1_subset_1(X61,u1_struct_0(X58))
        | ~ m1_subset_1(X60,u1_struct_0(X58))
        | v1_xboole_0(X59)
        | ~ v19_lattices(X59,X58)
        | ~ v20_lattices(X59,X58)
        | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
        | v2_struct_0(X58)
        | ~ v10_lattices(X58)
        | ~ v3_filter_0(X58)
        | ~ l3_lattices(X58) )
      & ( r2_hidden(k4_filter_0(X58,X60,k3_lattices(X58,X62,X61)),X59)
        | ~ r2_hidden(k4_filter_0(X58,X60,X61),X59)
        | ~ m1_subset_1(X62,u1_struct_0(X58))
        | ~ m1_subset_1(X61,u1_struct_0(X58))
        | ~ m1_subset_1(X60,u1_struct_0(X58))
        | v1_xboole_0(X59)
        | ~ v19_lattices(X59,X58)
        | ~ v20_lattices(X59,X58)
        | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
        | v2_struct_0(X58)
        | ~ v10_lattices(X58)
        | ~ v3_filter_0(X58)
        | ~ l3_lattices(X58) )
      & ( r2_hidden(k4_filter_0(X58,k4_lattices(X58,X60,X62),X61),X59)
        | ~ r2_hidden(k4_filter_0(X58,X60,X61),X59)
        | ~ m1_subset_1(X62,u1_struct_0(X58))
        | ~ m1_subset_1(X61,u1_struct_0(X58))
        | ~ m1_subset_1(X60,u1_struct_0(X58))
        | v1_xboole_0(X59)
        | ~ v19_lattices(X59,X58)
        | ~ v20_lattices(X59,X58)
        | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
        | v2_struct_0(X58)
        | ~ v10_lattices(X58)
        | ~ v3_filter_0(X58)
        | ~ l3_lattices(X58) )
      & ( r2_hidden(k4_filter_0(X58,k4_lattices(X58,X62,X60),X61),X59)
        | ~ r2_hidden(k4_filter_0(X58,X60,X61),X59)
        | ~ m1_subset_1(X62,u1_struct_0(X58))
        | ~ m1_subset_1(X61,u1_struct_0(X58))
        | ~ m1_subset_1(X60,u1_struct_0(X58))
        | v1_xboole_0(X59)
        | ~ v19_lattices(X59,X58)
        | ~ v20_lattices(X59,X58)
        | ~ m1_subset_1(X59,k1_zfmisc_1(u1_struct_0(X58)))
        | v2_struct_0(X58)
        | ~ v10_lattices(X58)
        | ~ v3_filter_0(X58)
        | ~ l3_lattices(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l66_filter_1])])])])])).

cnf(c_0_40,negated_conjecture,
    ( ~ r2_hidden(k4_lattices(esk1_0,k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),k4_filter_0(esk1_0,k4_lattices(esk1_0,esk4_0,esk6_0),k4_lattices(esk1_0,esk3_0,esk5_0))),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k3_lattices(esk1_0,esk4_0,esk6_0),k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k3_lattices(esk1_0,esk3_0,esk5_0),k3_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,k3_lattices(esk1_0,X1,X2),X3),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,X2,X3),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,X1,X3),esk2_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_32]),c_0_33]),c_0_22]),c_0_38]),c_0_23])]),c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,plain,
    ( r2_hidden(k4_filter_0(X1,X2,k3_lattices(X1,X3,X4)),X5)
    | v1_xboole_0(X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k4_filter_0(X1,X2,X4),X5)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v19_lattices(X5,X1)
    | ~ v20_lattices(X5,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( ~ r2_hidden(k4_lattices(esk1_0,k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),k4_filter_0(esk1_0,k4_lattices(esk1_0,esk4_0,esk6_0),k4_lattices(esk1_0,esk3_0,esk5_0))),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k3_lattices(esk1_0,esk3_0,esk5_0),k3_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42]),c_0_43])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_48,plain,
    ( r2_hidden(k4_filter_0(X1,X2,k3_lattices(X1,X3,X4)),X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k4_filter_0(X1,X2,X4),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v20_lattices(X5,X1)
    | ~ v19_lattices(X5,X1)
    | ~ l3_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_44,c_0_27])).

cnf(c_0_49,plain,
    ( r2_hidden(k4_filter_0(X1,X2,k3_lattices(X1,X3,X4)),X5)
    | v1_xboole_0(X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k4_filter_0(X1,X2,X3),X5)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v19_lattices(X5,X1)
    | ~ v20_lattices(X5,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(k4_lattices(esk1_0,k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),k4_filter_0(esk1_0,k4_lattices(esk1_0,esk4_0,esk6_0),k4_lattices(esk1_0,esk3_0,esk5_0))),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,k3_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,k3_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_41]),c_0_46]),c_0_47])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,X1,k3_lattices(esk1_0,X2,X3)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,X1,X3),esk2_0)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_31]),c_0_32]),c_0_33]),c_0_22]),c_0_38]),c_0_23])]),c_0_24])).

cnf(c_0_52,plain,
    ( r2_hidden(k4_filter_0(X1,X2,k3_lattices(X1,X3,X4)),X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k4_filter_0(X1,X2,X3),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v20_lattices(X5,X1)
    | ~ v19_lattices(X5,X1)
    | ~ l3_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_49,c_0_27])).

fof(c_0_53,plain,(
    ! [X31,X32,X33] :
      ( v2_struct_0(X31)
      | ~ v4_lattices(X31)
      | ~ l2_lattices(X31)
      | ~ m1_subset_1(X32,u1_struct_0(X31))
      | ~ m1_subset_1(X33,u1_struct_0(X31))
      | m1_subset_1(k3_lattices(X31,X32,X33),u1_struct_0(X31)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k3_lattices])])])).

fof(c_0_54,plain,(
    ! [X15] :
      ( ( ~ v2_struct_0(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v4_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v5_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v6_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v7_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v8_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) )
      & ( v9_lattices(X15)
        | v2_struct_0(X15)
        | ~ v10_lattices(X15)
        | ~ l3_lattices(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattices])])])])).

fof(c_0_55,plain,(
    ! [X49] :
      ( ( l1_lattices(X49)
        | ~ l3_lattices(X49) )
      & ( l2_lattices(X49)
        | ~ l3_lattices(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l3_lattices])])])).

cnf(c_0_56,negated_conjecture,
    ( ~ r2_hidden(k4_lattices(esk1_0,k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),k4_filter_0(esk1_0,k4_lattices(esk1_0,esk4_0,esk6_0),k4_lattices(esk1_0,esk3_0,esk5_0))),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,k3_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_42]),c_0_43]),c_0_46])])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,X1,k3_lattices(esk1_0,X2,X3)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,X1,X2),esk2_0)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_31]),c_0_32]),c_0_33]),c_0_22]),c_0_38]),c_0_23])]),c_0_24])).

cnf(c_0_58,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k3_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v4_lattices(X1)
    | ~ l2_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_59,plain,
    ( v4_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_60,plain,
    ( l2_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

fof(c_0_61,plain,(
    ! [X68,X69,X70,X71,X72] :
      ( v2_struct_0(X68)
      | ~ v10_lattices(X68)
      | ~ v3_filter_0(X68)
      | ~ l3_lattices(X68)
      | v1_xboole_0(X69)
      | ~ v19_lattices(X69,X68)
      | ~ v20_lattices(X69,X68)
      | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
      | ~ m1_subset_1(X70,u1_struct_0(X68))
      | ~ m1_subset_1(X71,u1_struct_0(X68))
      | ~ m1_subset_1(X72,u1_struct_0(X68))
      | ~ r2_hidden(k4_filter_0(X68,X70,X71),X69)
      | ~ r2_hidden(k4_filter_0(X68,X70,X72),X69)
      | r2_hidden(k4_filter_0(X68,X70,k4_lattices(X68,X71,X72)),X69) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l70_filter_1])])])])).

cnf(c_0_62,negated_conjecture,
    ( ~ r2_hidden(k4_lattices(esk1_0,k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),k4_filter_0(esk1_0,k4_lattices(esk1_0,esk4_0,esk6_0),k4_lattices(esk1_0,esk3_0,esk5_0))),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_42]),c_0_43]),c_0_47])])).

cnf(c_0_63,plain,
    ( m1_subset_1(k3_lattices(X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | v1_xboole_0(X2)
    | r2_hidden(k4_filter_0(X1,X3,k4_lattices(X1,X4,X5)),X2)
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ l3_lattices(X1)
    | ~ v19_lattices(X2,X1)
    | ~ v20_lattices(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ r2_hidden(k4_filter_0(X1,X3,X4),X2)
    | ~ r2_hidden(k4_filter_0(X1,X3,X5),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( ~ r2_hidden(k4_lattices(esk1_0,k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),k4_filter_0(esk1_0,k4_lattices(esk1_0,esk4_0,esk6_0),k4_lattices(esk1_0,esk3_0,esk5_0))),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_42]),c_0_43]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_66,plain,
    ( r2_hidden(k4_filter_0(X1,X2,k4_lattices(X1,X3,X4)),X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k4_filter_0(X1,X2,X4),X5)
    | ~ r2_hidden(k4_filter_0(X1,X2,X3),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v20_lattices(X5,X1)
    | ~ v19_lattices(X5,X1)
    | ~ l3_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_64,c_0_27])).

cnf(c_0_67,plain,
    ( r2_hidden(k4_filter_0(X1,k4_lattices(X1,X2,X3),X4),X5)
    | v1_xboole_0(X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k4_filter_0(X1,X3,X4),X5)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v19_lattices(X5,X1)
    | ~ v20_lattices(X5,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_68,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk4_0,esk6_0),k4_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_36])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,X1,k4_lattices(esk1_0,X2,X3)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,X1,X3),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,X1,X2),esk2_0)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_31]),c_0_32]),c_0_33]),c_0_22]),c_0_38]),c_0_23])]),c_0_24])).

cnf(c_0_70,plain,
    ( r2_hidden(k4_filter_0(X1,k4_lattices(X1,X2,X3),X4),X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k4_filter_0(X1,X3,X4),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v20_lattices(X5,X1)
    | ~ v19_lattices(X5,X1)
    | ~ l3_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_67,c_0_27])).

cnf(c_0_71,plain,
    ( r2_hidden(k4_filter_0(X1,k4_lattices(X1,X2,X3),X4),X5)
    | v1_xboole_0(X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k4_filter_0(X1,X2,X4),X5)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v19_lattices(X5,X1)
    | ~ v20_lattices(X5,X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v10_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk4_0,esk6_0),esk5_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk4_0,esk6_0),esk3_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_46]),c_0_47])])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,X1,X2),X3),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,X2,X3),esk2_0)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_31]),c_0_32]),c_0_33]),c_0_22]),c_0_38]),c_0_23])]),c_0_24])).

cnf(c_0_74,plain,
    ( r2_hidden(k4_filter_0(X1,k4_lattices(X1,X2,X3),X4),X5)
    | v2_struct_0(X1)
    | ~ r2_hidden(k4_filter_0(X1,X2,X4),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v20_lattices(X5,X1)
    | ~ v19_lattices(X5,X1)
    | ~ l3_lattices(X1)
    | ~ v3_filter_0(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[c_0_71,c_0_27])).

cnf(c_0_75,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(k4_lattices(X3,X4,X1),X2)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ v19_lattices(X2,X3)
    | ~ v20_lattices(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_76,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk4_0,esk6_0),esk3_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,esk5_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_46]),c_0_42]),c_0_43])])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,X1,X2),X3),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,X1,X3),esk2_0)
    | ~ m1_subset_1(X3,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_31]),c_0_32]),c_0_33]),c_0_22]),c_0_38]),c_0_23])]),c_0_24])).

cnf(c_0_78,plain,
    ( v2_struct_0(X3)
    | v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3)
    | ~ v19_lattices(X2,X3)
    | ~ v20_lattices(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(k4_lattices(X3,X4,X1),X2) ),
    inference(cn,[status(thm)],[c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( r2_hidden(k7_filter_0(esk1_0,esk5_0,esk6_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_80,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,esk5_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_47]),c_0_42]),c_0_43])])).

cnf(c_0_81,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(k4_lattices(X3,X4,X1),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v20_lattices(X2,X3)
    | ~ v19_lattices(X2,X3)
    | ~ l3_lattices(X3)
    | ~ v10_lattices(X3) ),
    inference(csr,[status(thm)],[c_0_78,c_0_27])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(k4_lattices(esk1_0,k4_filter_0(esk1_0,esk5_0,esk6_0),k4_filter_0(esk1_0,esk6_0,esk5_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_21]),c_0_42]),c_0_46]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_83,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk6_0,esk5_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_51]),c_0_46]),c_0_47]),c_0_42])])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,esk6_0,esk5_0),esk2_0)
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk5_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk6_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_32]),c_0_31]),c_0_33]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_32])).

fof(c_0_86,plain,(
    ! [X38,X39,X40] :
      ( v2_struct_0(X38)
      | ~ v10_lattices(X38)
      | ~ l3_lattices(X38)
      | ~ m1_subset_1(X39,u1_struct_0(X38))
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | m1_subset_1(k4_filter_0(X38,X39,X40),u1_struct_0(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_filter_0])])])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(k4_lattices(X3,X1,X4),X2)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v19_lattices(X2,X3)
    | ~ v20_lattices(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_88,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk6_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_85])).

cnf(c_0_89,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_filter_0(X1,X2,X3),u1_struct_0(X1))
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_86])).

cnf(c_0_90,plain,
    ( v2_struct_0(X3)
    | v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ v10_lattices(X3)
    | ~ l3_lattices(X3)
    | ~ v19_lattices(X2,X3)
    | ~ v20_lattices(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r2_hidden(k4_lattices(X3,X1,X4),X2) ),
    inference(cn,[status(thm)],[c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),k4_lattices(esk1_0,esk4_0,esk6_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_46]),c_0_42]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_92,plain,
    ( r2_hidden(X1,X2)
    | v2_struct_0(X3)
    | ~ r2_hidden(k4_lattices(X3,X1,X4),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X4,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v20_lattices(X2,X3)
    | ~ v19_lattices(X2,X3)
    | ~ l3_lattices(X3)
    | ~ v10_lattices(X3) ),
    inference(csr,[status(thm)],[c_0_90,c_0_27])).

cnf(c_0_93,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_69]),c_0_42]),c_0_43])])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk6_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk5_0,esk6_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_82]),c_0_32]),c_0_31]),c_0_33]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_95,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_73]),c_0_42]),c_0_46]),c_0_47])])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,esk5_0,esk6_0),esk2_0)
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk5_0,esk6_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_89]),c_0_46]),c_0_42]),c_0_22]),c_0_23])]),c_0_24])).

fof(c_0_97,plain,(
    ! [X41,X42,X43] :
      ( v2_struct_0(X41)
      | ~ v6_lattices(X41)
      | ~ l1_lattices(X41)
      | ~ m1_subset_1(X42,u1_struct_0(X41))
      | ~ m1_subset_1(X43,u1_struct_0(X41))
      | m1_subset_1(k4_lattices(X41,X42,X43),u1_struct_0(X41)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k4_lattices])])])).

cnf(c_0_98,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk5_0,esk6_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_95,c_0_96])).

cnf(c_0_99,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | ~ v6_lattices(X1)
    | ~ l1_lattices(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_97])).

cnf(c_0_100,plain,
    ( v6_lattices(X1)
    | v2_struct_0(X1)
    | ~ v10_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_101,plain,
    ( l1_lattices(X1)
    | ~ l3_lattices(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_102,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk4_0,esk6_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_89]),c_0_42]),c_0_46]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_103,plain,
    ( m1_subset_1(k4_lattices(X1,X2,X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l3_lattices(X1)
    | ~ v10_lattices(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_100]),c_0_101])).

cnf(c_0_104,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,k3_lattices(esk1_0,esk3_0,esk5_0)),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_102,c_0_103]),c_0_42]),c_0_43]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_105,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k3_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_57]),c_0_46]),c_0_47]),c_0_43])])).

cnf(c_0_106,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,k4_lattices(esk1_0,esk3_0,esk5_0),esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_63]),c_0_46]),c_0_47]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_107,negated_conjecture,
    ( r2_hidden(k7_filter_0(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_108,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k4_lattices(esk1_0,esk3_0,esk5_0),u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_106,c_0_77]),c_0_43]),c_0_46]),c_0_47])])).

cnf(c_0_109,negated_conjecture,
    ( r2_hidden(k4_lattices(esk1_0,k4_filter_0(esk1_0,esk3_0,esk4_0),k4_filter_0(esk1_0,esk4_0,esk3_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_21]),c_0_43]),c_0_47]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_110,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_103]),c_0_46]),c_0_47]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_111,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,esk4_0,esk3_0),esk2_0)
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk3_0,esk4_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_109]),c_0_32]),c_0_31]),c_0_33]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_112,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_111]),c_0_85])).

cnf(c_0_113,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk4_0,esk3_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk3_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_109]),c_0_32]),c_0_31]),c_0_33]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_114,negated_conjecture,
    ( ~ r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_89]),c_0_47]),c_0_43]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_115,negated_conjecture,
    ( r2_hidden(k4_filter_0(esk1_0,esk3_0,esk4_0),esk2_0)
    | ~ m1_subset_1(k4_filter_0(esk1_0,esk3_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_113,c_0_89]),c_0_47]),c_0_43]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_116,negated_conjecture,
    ( ~ m1_subset_1(k4_filter_0(esk1_0,esk3_0,esk4_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_114,c_0_115])).

cnf(c_0_117,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_89]),c_0_43]),c_0_47]),c_0_22]),c_0_23])]),c_0_24]),
    [proof]).
%------------------------------------------------------------------------------
