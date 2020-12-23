%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1674+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9QLwnGK9Mj

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:00 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       : 1136 (3349308309101691797504 expanded)
%              Number of leaves         :   55 (937393053968438525952 expanded)
%              Depth                    :  416
%              Number of atoms          : 22841 (128202598270853177147392 expanded)
%              Number of equality atoms : 1129 (5244489078264408571904 expanded)
%              Maximal formula depth    :   22 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(zip_tseitin_5_type,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_6_type,type,(
    zip_tseitin_6: $i > $i > $o )).

thf(zip_tseitin_8_type,type,(
    zip_tseitin_8: $i > $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(zip_tseitin_4_type,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_7_type,type,(
    zip_tseitin_7: $i > $i > $i > $o )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(r2_lattice3_type,type,(
    r2_lattice3: $i > $i > $i > $o )).

thf(t54_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ! [D: $i] :
                      ( ( ( v1_finset_1 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r1_yellow_0 @ A @ D ) ) )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r2_hidden @ D @ C )
                          & ! [E: $i] :
                              ( ( ( v1_finset_1 @ E )
                                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
                             => ~ ( ( r1_yellow_0 @ A @ E )
                                  & ( D
                                    = ( k1_yellow_0 @ A @ E ) ) ) ) ) )
                  & ! [D: $i] :
                      ( ( ( v1_finset_1 @ D )
                        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) )
                  & ( r1_yellow_0 @ A @ B ) )
               => ( ( k1_yellow_0 @ A @ C )
                  = ( k1_yellow_0 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( ( ! [D: $i] :
                        ( ( ( v1_finset_1 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                       => ( ( D != k1_xboole_0 )
                         => ( r1_yellow_0 @ A @ D ) ) )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                       => ~ ( ( r2_hidden @ D @ C )
                            & ! [E: $i] :
                                ( ( ( v1_finset_1 @ E )
                                  & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
                               => ~ ( ( r1_yellow_0 @ A @ E )
                                    & ( D
                                      = ( k1_yellow_0 @ A @ E ) ) ) ) ) )
                    & ! [D: $i] :
                        ( ( ( v1_finset_1 @ D )
                          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) )
                       => ( ( D != k1_xboole_0 )
                         => ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) )
                    & ( r1_yellow_0 @ A @ B ) )
                 => ( ( k1_yellow_0 @ A @ C )
                    = ( k1_yellow_0 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t54_waybel_0])).

thf('0',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t47_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ( r1_yellow_0 @ A @ B )
            & ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r2_lattice3 @ A @ B @ D )
                <=> ( r2_lattice3 @ A @ C @ D ) ) ) )
         => ( ( k1_yellow_0 @ A @ B )
            = ( k1_yellow_0 @ A @ C ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf(t52_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v3_orders_2 @ A )
        & ~ ( v2_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ! [D: $i] :
                      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) )
                        & ( v1_finset_1 @ D ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) ) )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ~ ( ! [E: $i] :
                              ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) )
                                & ( v1_finset_1 @ E ) )
                             => ~ ( ( D
                                    = ( k1_yellow_0 @ A @ E ) )
                                  & ( r1_yellow_0 @ A @ E ) ) )
                          & ( r2_hidden @ D @ C ) ) )
                  & ! [D: $i] :
                      ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) )
                        & ( v1_finset_1 @ D ) )
                     => ( ( D != k1_xboole_0 )
                       => ( r1_yellow_0 @ A @ D ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r2_lattice3 @ A @ B @ D )
                    <=> ( r2_lattice3 @ A @ C @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
       => ~ ( zip_tseitin_3 @ D @ C @ B @ A ) )
     => ( zip_tseitin_4 @ D @ C @ B @ A ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('15',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(zf_stmt_2,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_0 @ D @ B )
       => ( zip_tseitin_1 @ D @ C @ A ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_8: $i > $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_8 @ D @ C @ B @ A )
     => ( ( r2_lattice3 @ A @ B @ D )
      <=> ( r2_lattice3 @ A @ C @ D ) ) ) )).

thf(zf_stmt_5,type,(
    zip_tseitin_7: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,B: $i,A: $i] :
      ( ( ( zip_tseitin_5 @ D @ B )
       => ( zip_tseitin_6 @ D @ A ) )
     => ( zip_tseitin_7 @ D @ B @ A ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_6: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [D: $i,A: $i] :
      ( ( ( D != k1_xboole_0 )
       => ( r1_yellow_0 @ A @ D ) )
     => ( zip_tseitin_6 @ D @ A ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_5: $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [D: $i,B: $i] :
      ( ( zip_tseitin_5 @ D @ B )
     => ( ( v1_finset_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_11,type,(
    zip_tseitin_4: $i > $i > $i > $i > $o )).

thf(zf_stmt_12,type,(
    zip_tseitin_3: $i > $i > $i > $i > $o )).

thf(zf_stmt_13,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ D @ C @ B @ A )
     => ( ( r2_hidden @ D @ C )
        & ! [E: $i] :
            ( ( ( v1_finset_1 @ E )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ B ) ) )
           => ~ ( ( r1_yellow_0 @ A @ E )
                & ( D
                  = ( k1_yellow_0 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_14,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_15,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_16,axiom,(
    ! [D: $i,C: $i,A: $i] :
      ( ( ( D != k1_xboole_0 )
       => ( r2_hidden @ ( k1_yellow_0 @ A @ D ) @ C ) )
     => ( zip_tseitin_1 @ D @ C @ A ) ) )).

thf(zf_stmt_17,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_18,axiom,(
    ! [D: $i,B: $i] :
      ( ( zip_tseitin_0 @ D @ B )
     => ( ( v1_finset_1 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_19,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( ! [D: $i] :
                      ( zip_tseitin_7 @ D @ B @ A )
                  & ! [D: $i] :
                      ( zip_tseitin_4 @ D @ C @ B @ A )
                  & ! [D: $i] :
                      ( zip_tseitin_2 @ D @ C @ B @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( zip_tseitin_8 @ D @ C @ B @ A ) ) ) ) ) ) )).

thf('22',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ X35 @ X36 ) @ X35 @ X36 )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X37 @ X35 @ X36 ) @ X37 @ X35 @ X36 )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X37 @ X35 @ X36 ) @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( u1_struct_0 @ X36 ) )
      | ( zip_tseitin_8 @ X38 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( l1_orders_2 @ X36 )
      | ~ ( v4_orders_2 @ X36 )
      | ~ ( v3_orders_2 @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_19])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ( zip_tseitin_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('44',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_7 @ X28 @ X29 @ X30 )
      | ( zip_tseitin_5 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('53',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['51','56'])).

thf('58',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('62',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['58','59'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('80',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('81',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['78','85'])).

thf('87',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('90',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('95',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('96',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['94','97'])).

thf('99',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['77'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('102',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_finset_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ( X15
       != ( k1_yellow_0 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('107',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['105','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['87','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['39','118'])).

thf('120',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('124',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['122','125'])).

thf('127',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['127','128'])).

thf('130',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['120','121'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['129','138'])).

thf('140',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_finset_1 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('144',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('146',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('147',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X39 ) @ sk_C )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('149',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('150',plain,(
    ! [X39: $i] :
      ( ( X39 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X39 ) @ sk_C )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['147','150'])).

thf('152',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['144','151'])).

thf('153',plain,
    ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X10 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('155',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','162'])).

thf('166',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['164','169'])).

thf('171',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['170'])).

thf('172',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['171','172'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('175',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['173','176'])).

thf('178',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['178','179'])).

thf('181',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['171','172'])).

thf('182',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('183',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['181','182'])).

thf('184',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['187','188'])).

thf('190',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['180','189'])).

thf('191',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['190'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('194',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('196',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['191','196'])).

thf('198',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['190'])).

thf('200',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('201',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['199','202'])).

thf('204',plain,
    ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['203'])).

thf('205',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['190'])).

thf('206',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('207',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('208',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['205','208'])).

thf('210',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['190'])).

thf('212',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','193'])).

thf('213',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['211','214'])).

thf('216',plain,
    ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['215'])).

thf('217',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['210','218'])).

thf('220',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['219'])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['204','220'])).

thf('222',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['198','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['223'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['163','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('227',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('228',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['226','227'])).

thf('229',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','228'])).

thf('230',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['230','231'])).

thf('233',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['225'])).

thf('234',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['233','234'])).

thf('236',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['232','235'])).

thf('237',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['237','238'])).

thf('240',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['230','231'])).

thf('241',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('242',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['242','243','244'])).

thf('246',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['245'])).

thf('247',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['246','247'])).

thf('249',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['239','248'])).

thf('250',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('252',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('253',plain,(
    ! [X24: $i,X25: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('254',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_3 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['252','253'])).

thf('255',plain,(
    ! [X41: $i] :
      ( ( X41 = k1_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('257',plain,(
    ! [X41: $i] :
      ( ( X41 = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('258',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['254','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('260',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('261',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['250','251'])).

thf('262',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_finset_1 @ X24 )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('263',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['261','262'])).

thf('264',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('265',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('267',plain,(
    ! [X9: $i,X10: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X9 @ X10 ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('269',plain,(
    ! [X9: $i,X10: $i] :
      ( zip_tseitin_1 @ o_0_0_xboole_0 @ X9 @ X10 ) ),
    inference(demod,[status(thm)],['267','268'])).

thf('270',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('271',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['265','271','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['260','273'])).

thf('275',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('276',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['260','273'])).

thf('277',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('279',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('280',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['278','279'])).

thf('281',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['275','280'])).

thf('282',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['281'])).

thf('283',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['282','283'])).

thf('285',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['276','277'])).

thf('286',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('287',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['285','286'])).

thf('288',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['284','287'])).

thf('289',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['288'])).

thf('290',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['289','290'])).

thf('292',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['282','283'])).

thf('293',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('294',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['292','293'])).

thf('295',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('297',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['294','295','296'])).

thf('298',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['297'])).

thf('299',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['298','299'])).

thf('301',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['291','300'])).

thf('302',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['301'])).

thf('303',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['301'])).

thf('304',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('305',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('306',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['305','306'])).

thf('308',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['302','307'])).

thf('309',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['308'])).

thf('310',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['301'])).

thf('311',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('312',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['311','312'])).

thf('314',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['310','313'])).

thf('315',plain,
    ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['314'])).

thf('316',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['301'])).

thf('317',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('318',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['317','318'])).

thf('320',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['316','319'])).

thf('321',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['320'])).

thf('322',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['301'])).

thf('323',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['303','304'])).

thf('324',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['323','324'])).

thf('326',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['322','325'])).

thf('327',plain,
    ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['326'])).

thf('328',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('329',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['327','328'])).

thf('330',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['321','329'])).

thf('331',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['330'])).

thf('332',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['315','331'])).

thf('333',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['332'])).

thf('334',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['309','333'])).

thf('335',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['334'])).

thf('336',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['274','335'])).

thf('337',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['336'])).

thf('338',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('339',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['337','338'])).

thf('340',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['259','339'])).

thf('341',plain,
    ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['340'])).

thf('342',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('343',plain,
    ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['341','342'])).

thf('344',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['336'])).

thf('345',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('346',plain,(
    ! [X0: $i] :
      ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['344','345'])).

thf('347',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['343','346'])).

thf('348',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['347'])).

thf('349',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('350',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['348','349'])).

thf('351',plain,
    ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['341','342'])).

thf('352',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('353',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['351','352'])).

thf('354',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('355',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['353','354','355'])).

thf('357',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['356'])).

thf('358',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('359',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['357','358'])).

thf('360',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['350','359'])).

thf('361',plain,
    ( ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['360'])).

thf('362',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_finset_1 @ X24 )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('363',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['361','362'])).

thf('364',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('365',plain,(
    v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['363','364'])).

thf('366',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['258','365'])).

thf('367',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_6 @ X26 @ X27 )
      | ~ ( r1_yellow_0 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('368',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_6 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['366','367'])).

thf('369',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_7 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_6 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('370',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['368','369'])).

thf('371',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('372',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['370','371'])).

thf('373',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','372'])).

thf('374',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','373'])).

thf('375',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','374'])).

thf('376',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','375'])).

thf('377',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('378',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','375'])).

thf('379',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('380',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['378','379'])).

thf('381',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('382',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['380','381'])).

thf('383',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['377','382'])).

thf('384',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['383'])).

thf('385',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('386',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['384','385'])).

thf('387',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['378','379'])).

thf('388',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('389',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['387','388'])).

thf('390',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['386','389'])).

thf('391',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['390'])).

thf('392',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('393',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['391','392'])).

thf('394',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['384','385'])).

thf('395',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('396',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['394','395'])).

thf('397',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('398',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('399',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['396','397','398'])).

thf('400',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['399'])).

thf('401',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('402',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['400','401'])).

thf('403',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['393','402'])).

thf('404',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['403'])).

thf('405',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['403'])).

thf('406',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('407',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['405','406'])).

thf('408',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('409',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['407','408'])).

thf('410',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['404','409'])).

thf('411',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['410'])).

thf('412',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['403'])).

thf('413',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['405','406'])).

thf('414',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('415',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['413','414'])).

thf('416',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['412','415'])).

thf('417',plain,
    ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['416'])).

thf('418',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['403'])).

thf('419',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['405','406'])).

thf('420',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('421',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['419','420'])).

thf('422',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['418','421'])).

thf('423',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['422'])).

thf('424',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['403'])).

thf('425',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['405','406'])).

thf('426',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('427',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['425','426'])).

thf('428',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['424','427'])).

thf('429',plain,
    ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['428'])).

thf('430',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('431',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['429','430'])).

thf('432',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['423','431'])).

thf('433',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['432'])).

thf('434',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['417','433'])).

thf('435',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['434'])).

thf('436',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['411','435'])).

thf('437',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['436'])).

thf('438',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['376','437'])).

thf('439',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['438'])).

thf('440',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('441',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['439','440'])).

thf('442',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['32','441'])).

thf('443',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['442'])).

thf('444',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('445',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['443','444'])).

thf('446',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['438'])).

thf('447',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('448',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['446','447'])).

thf('449',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['445','448'])).

thf('450',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['449'])).

thf('451',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('452',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['450','451'])).

thf('453',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['443','444'])).

thf('454',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('455',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['453','454'])).

thf('456',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('457',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('458',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['455','456','457'])).

thf('459',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['458'])).

thf('460',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('461',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['459','460'])).

thf('462',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['452','461'])).

thf('463',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['462'])).

thf('464',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_finset_1 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('465',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['463','464'])).

thf('466',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['462'])).

thf('467',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('468',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['466','467'])).

thf('469',plain,(
    ! [X39: $i] :
      ( ( X39 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X39 ) @ sk_C )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('470',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['468','469'])).

thf('471',plain,
    ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
    | ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['470'])).

thf('472',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['465','471'])).

thf('473',plain,
    ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['472'])).

thf('474',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X10 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('475',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['473','474'])).

thf('476',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('477',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_2 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['475','476'])).

thf('478',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','372'])).

thf('479',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['477','478'])).

thf('480',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('481',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['479','480'])).

thf('482',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['481'])).

thf('483',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','482'])).

thf('484',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('485',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','482'])).

thf('486',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('487',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['485','486'])).

thf('488',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('489',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['487','488'])).

thf('490',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['484','489'])).

thf('491',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['490'])).

thf('492',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('493',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['491','492'])).

thf('494',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['485','486'])).

thf('495',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('496',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['494','495'])).

thf('497',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['493','496'])).

thf('498',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['497'])).

thf('499',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('500',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['498','499'])).

thf('501',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['491','492'])).

thf('502',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('503',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['501','502'])).

thf('504',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('505',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('506',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['503','504','505'])).

thf('507',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['506'])).

thf('508',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('509',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['507','508'])).

thf('510',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['500','509'])).

thf('511',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['510'])).

thf('512',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['510'])).

thf('513',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('514',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['512','513'])).

thf('515',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('516',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['514','515'])).

thf('517',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['511','516'])).

thf('518',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['517'])).

thf('519',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['510'])).

thf('520',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['512','513'])).

thf('521',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('522',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['520','521'])).

thf('523',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['519','522'])).

thf('524',plain,
    ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['523'])).

thf('525',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['510'])).

thf('526',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['512','513'])).

thf('527',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('528',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['526','527'])).

thf('529',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['525','528'])).

thf('530',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['529'])).

thf('531',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['510'])).

thf('532',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['512','513'])).

thf('533',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('534',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['532','533'])).

thf('535',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['531','534'])).

thf('536',plain,
    ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['535'])).

thf('537',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('538',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['536','537'])).

thf('539',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['530','538'])).

thf('540',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['539'])).

thf('541',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['524','540'])).

thf('542',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['541'])).

thf('543',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['518','542'])).

thf('544',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['543'])).

thf('545',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['483','544'])).

thf('546',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['545'])).

thf('547',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('548',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['546','547'])).

thf('549',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','548'])).

thf('550',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['549'])).

thf('551',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('552',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['550','551'])).

thf('553',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['545'])).

thf('554',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('555',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['553','554'])).

thf('556',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['552','555'])).

thf('557',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['556'])).

thf('558',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('559',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['557','558'])).

thf('560',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['550','551'])).

thf('561',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('562',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['560','561'])).

thf('563',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('564',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('565',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['562','563','564'])).

thf('566',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['565'])).

thf('567',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('568',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['566','567'])).

thf('569',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['559','568'])).

thf('570',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['569'])).

thf('571',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('572',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['570','571'])).

thf('573',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_4 @ X20 @ X21 @ X22 @ X23 )
      | ( zip_tseitin_3 @ X20 @ X21 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('574',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('575',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('576',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['570','571'])).

thf('577',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('578',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['576','577'])).

thf('579',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('580',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('581',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['578','579','580'])).

thf('582',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['575','581'])).

thf('583',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('584',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['575','581'])).

thf('585',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('586',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['584','585'])).

thf('587',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('588',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['586','587'])).

thf('589',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['583','588'])).

thf('590',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['589'])).

thf('591',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('592',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['590','591'])).

thf('593',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['584','585'])).

thf('594',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('595',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['593','594'])).

thf('596',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['592','595'])).

thf('597',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['596'])).

thf('598',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('599',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['597','598'])).

thf('600',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['590','591'])).

thf('601',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('602',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['600','601'])).

thf('603',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('604',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('605',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['602','603','604'])).

thf('606',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['605'])).

thf('607',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('608',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['606','607'])).

thf('609',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['599','608'])).

thf('610',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['609'])).

thf('611',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['609'])).

thf('612',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('613',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['611','612'])).

thf('614',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('615',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['613','614'])).

thf('616',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['610','615'])).

thf('617',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['616'])).

thf('618',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['609'])).

thf('619',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['611','612'])).

thf('620',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('621',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['619','620'])).

thf('622',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['618','621'])).

thf('623',plain,
    ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['622'])).

thf('624',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['609'])).

thf('625',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['611','612'])).

thf('626',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('627',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['625','626'])).

thf('628',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['624','627'])).

thf('629',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['628'])).

thf('630',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['609'])).

thf('631',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['611','612'])).

thf('632',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('633',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['631','632'])).

thf('634',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['630','633'])).

thf('635',plain,
    ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['634'])).

thf('636',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('637',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['635','636'])).

thf('638',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['629','637'])).

thf('639',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['638'])).

thf('640',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['623','639'])).

thf('641',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['640'])).

thf('642',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['617','641'])).

thf('643',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['642'])).

thf('644',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['582','643'])).

thf('645',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['644'])).

thf('646',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('647',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['645','646'])).

thf('648',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['574','647'])).

thf('649',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['648'])).

thf('650',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('651',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['649','650'])).

thf('652',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['644'])).

thf('653',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('654',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['652','653'])).

thf('655',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['651','654'])).

thf('656',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['655'])).

thf('657',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('658',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['656','657'])).

thf('659',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['649','650'])).

thf('660',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('661',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['659','660'])).

thf('662',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('663',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('664',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['661','662','663'])).

thf('665',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['664'])).

thf('666',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('667',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['665','666'])).

thf('668',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['658','667'])).

thf('669',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['668'])).

thf('670',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('671',plain,
    ( ( zip_tseitin_5 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['669','670'])).

thf('672',plain,(
    ! [X24: $i,X25: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( zip_tseitin_5 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('673',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_3 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['671','672'])).

thf('674',plain,(
    ! [X41: $i] :
      ( ( X41 = o_0_0_xboole_0 )
      | ( r1_yellow_0 @ sk_A @ X41 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['255','256'])).

thf('675',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['673','674'])).

thf('676',plain,(
    v1_finset_1 @ ( sk_D_3 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['363','364'])).

thf('677',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['675','676'])).

thf('678',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_D_3 @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['677'])).

thf('679',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_6 @ X26 @ X27 )
      | ~ ( r1_yellow_0 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('680',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_6 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['678','679'])).

thf('681',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_7 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_6 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('682',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['680','681'])).

thf('683',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_7 @ ( sk_D_3 @ sk_B @ sk_A ) @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('684',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['682','683'])).

thf('685',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['573','684'])).

thf('686',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['572','685'])).

thf('687',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('688',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('689',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['686','687','688'])).

thf('690',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['689'])).

thf('691',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','690'])).

thf('692',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('693',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','690'])).

thf('694',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('695',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['693','694'])).

thf('696',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('697',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['695','696'])).

thf('698',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['692','697'])).

thf('699',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['698'])).

thf('700',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('701',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['699','700'])).

thf('702',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['693','694'])).

thf('703',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('704',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['702','703'])).

thf('705',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['701','704'])).

thf('706',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['705'])).

thf('707',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('708',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['706','707'])).

thf('709',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['699','700'])).

thf('710',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('711',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['709','710'])).

thf('712',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('713',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('714',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['711','712','713'])).

thf('715',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['714'])).

thf('716',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('717',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['715','716'])).

thf('718',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['708','717'])).

thf('719',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['718'])).

thf('720',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('721',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['719','720'])).

thf('722',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('723',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['721','722'])).

thf('724',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('725',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['723','724'])).

thf('726',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['719','720'])).

thf('727',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['725','726'])).

thf('728',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['721','722'])).

thf('729',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('730',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['728','729'])).

thf('731',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['719','720'])).

thf('732',plain,
    ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['730','731'])).

thf('733',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['721','722'])).

thf('734',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('735',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['733','734'])).

thf('736',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['719','720'])).

thf('737',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['735','736'])).

thf('738',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['721','722'])).

thf('739',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('740',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['738','739'])).

thf('741',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['719','720'])).

thf('742',plain,
    ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['740','741'])).

thf('743',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('744',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['742','743'])).

thf('745',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['737','744'])).

thf('746',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['745'])).

thf('747',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['732','746'])).

thf('748',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['747'])).

thf('749',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['727','748'])).

thf('750',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['749'])).

thf('751',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['691','750'])).

thf('752',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['751'])).

thf('753',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('754',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['752','753'])).

thf('755',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['28','754'])).

thf('756',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['755'])).

thf('757',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('758',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['756','757'])).

thf('759',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('760',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['758','759'])).

thf('761',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['751'])).

thf('762',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('763',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_3 @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['761','762'])).

thf('764',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['760','763'])).

thf('765',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['764'])).

thf('766',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('767',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['765','766'])).

thf('768',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('769',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['767','768'])).

thf('770',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['758','759'])).

thf('771',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('772',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['770','771'])).

thf('773',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('774',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('775',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['772','773','774'])).

thf('776',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('777',plain,
    ( ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['775','776'])).

thf('778',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('779',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_3 @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['777','778'])).

thf('780',plain,
    ( ( sk_D_3 @ sk_B @ sk_A )
    = o_0_0_xboole_0 ),
    inference(clc,[status(thm)],['769','779'])).

thf('781',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_6 @ X26 @ X27 )
      | ( X26 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('782',plain,(
    ! [X27: $i] :
      ( zip_tseitin_6 @ k1_xboole_0 @ X27 ) ),
    inference(simplify,[status(thm)],['781'])).

thf('783',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('784',plain,(
    ! [X27: $i] :
      ( zip_tseitin_6 @ o_0_0_xboole_0 @ X27 ) ),
    inference(demod,[status(thm)],['782','783'])).

thf('785',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( zip_tseitin_7 @ X28 @ X29 @ X30 )
      | ~ ( zip_tseitin_6 @ X28 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('786',plain,(
    ! [X0: $i,X1: $i] :
      ( zip_tseitin_7 @ o_0_0_xboole_0 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['784','785'])).

thf('787',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','780','786'])).

thf('788',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','787'])).

thf('789',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','788'])).

thf('790',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','789'])).

thf('791',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','790'])).

thf('792',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('793',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','790'])).

thf('794',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('795',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['793','794'])).

thf('796',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('797',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['795','796'])).

thf('798',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['792','797'])).

thf('799',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['798'])).

thf('800',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('801',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['799','800'])).

thf('802',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['793','794'])).

thf('803',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('804',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['802','803'])).

thf('805',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['801','804'])).

thf('806',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['805'])).

thf('807',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('808',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['806','807'])).

thf('809',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['799','800'])).

thf('810',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('811',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['809','810'])).

thf('812',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('813',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('814',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['811','812','813'])).

thf('815',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['814'])).

thf('816',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('817',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['815','816'])).

thf('818',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['808','817'])).

thf('819',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['818'])).

thf('820',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('821',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['819','820'])).

thf('822',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('823',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['821','822'])).

thf('824',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('825',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['823','824'])).

thf('826',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['819','820'])).

thf('827',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['825','826'])).

thf('828',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['821','822'])).

thf('829',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('830',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['828','829'])).

thf('831',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['819','820'])).

thf('832',plain,
    ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['830','831'])).

thf('833',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['821','822'])).

thf('834',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('835',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['833','834'])).

thf('836',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['819','820'])).

thf('837',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['835','836'])).

thf('838',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['821','822'])).

thf('839',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('840',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['838','839'])).

thf('841',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['819','820'])).

thf('842',plain,
    ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['840','841'])).

thf('843',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('844',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['842','843'])).

thf('845',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['837','844'])).

thf('846',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['845'])).

thf('847',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['832','846'])).

thf('848',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['847'])).

thf('849',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['827','848'])).

thf('850',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['849'])).

thf('851',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['791','850'])).

thf('852',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['851'])).

thf('853',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('854',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['852','853'])).

thf('855',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','854'])).

thf('856',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['855'])).

thf('857',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('858',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['856','857'])).

thf('859',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('860',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['858','859'])).

thf('861',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ) ),
    inference(simplify,[status(thm)],['851'])).

thf('862',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('863',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['861','862'])).

thf('864',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['860','863'])).

thf('865',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['864'])).

thf('866',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('867',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['865','866'])).

thf('868',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('869',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['867','868'])).

thf('870',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['858','859'])).

thf('871',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('872',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['870','871'])).

thf('873',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('874',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('875',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['872','873','874'])).

thf('876',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('877',plain,
    ( ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['875','876'])).

thf('878',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('879',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['877','878'])).

thf('880',plain,(
    zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['869','879'])).

thf('881',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('882',plain,(
    m1_subset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['880','881'])).

thf('883',plain,(
    ! [X39: $i] :
      ( ( X39 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ X39 ) @ sk_C )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( v1_finset_1 @ X39 ) ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('884',plain,
    ( ~ ( v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['882','883'])).

thf('885',plain,(
    zip_tseitin_0 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_B ),
    inference(clc,[status(thm)],['869','879'])).

thf('886',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_finset_1 @ X6 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_18])).

thf('887',plain,(
    v1_finset_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['885','886'])).

thf('888',plain,
    ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['884','887'])).

thf('889',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( zip_tseitin_1 @ X8 @ X9 @ X10 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X10 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_16])).

thf('890',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( zip_tseitin_1 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['888','889'])).

thf('891',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_2 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( zip_tseitin_1 @ X11 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('892',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_2 @ ( sk_D_2 @ sk_C @ sk_B @ sk_A ) @ sk_C @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['890','891'])).

thf('893',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','780','786'])).

thf('894',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['892','893'])).

thf('895',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('896',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['894','895'])).

thf('897',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','896'])).

thf('898',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','897'])).

thf('899',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('900',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','897'])).

thf('901',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('902',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['900','901'])).

thf('903',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('904',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['902','903'])).

thf('905',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['899','904'])).

thf('906',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['905'])).

thf('907',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('908',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['906','907'])).

thf('909',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['900','901'])).

thf('910',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('911',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['909','910'])).

thf('912',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['908','911'])).

thf('913',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['912'])).

thf('914',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('915',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['913','914'])).

thf('916',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['906','907'])).

thf('917',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('918',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['916','917'])).

thf('919',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('920',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('921',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['918','919','920'])).

thf('922',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['921'])).

thf('923',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('924',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['922','923'])).

thf('925',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['915','924'])).

thf('926',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['925'])).

thf('927',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('928',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['926','927'])).

thf('929',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('930',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['928','929'])).

thf('931',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('932',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['930','931'])).

thf('933',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['926','927'])).

thf('934',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['932','933'])).

thf('935',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['928','929'])).

thf('936',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('937',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['935','936'])).

thf('938',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['926','927'])).

thf('939',plain,
    ( ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['937','938'])).

thf('940',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['928','929'])).

thf('941',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('942',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['940','941'])).

thf('943',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['926','927'])).

thf('944',plain,
    ( ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['942','943'])).

thf('945',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['928','929'])).

thf('946',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('947',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['945','946'])).

thf('948',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['926','927'])).

thf('949',plain,
    ( ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['947','948'])).

thf('950',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('951',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['949','950'])).

thf('952',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['944','951'])).

thf('953',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['952'])).

thf('954',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['939','953'])).

thf('955',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['954'])).

thf('956',plain,(
    ! [X0: $i] :
      ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['934','955'])).

thf('957',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['956'])).

thf('958',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['898','957'])).

thf('959',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['958'])).

thf('960',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('961',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['959','960'])).

thf('962',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','961'])).

thf('963',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['962'])).

thf('964',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('965',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['963','964'])).

thf('966',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('967',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['965','966'])).

thf('968',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['958'])).

thf('969',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('970',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
        = o_0_0_xboole_0 )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['968','969'])).

thf('971',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['967','970'])).

thf('972',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['971'])).

thf('973',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('974',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['972','973'])).

thf('975',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('976',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['974','975'])).

thf('977',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['965','966'])).

thf('978',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('979',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['977','978'])).

thf('980',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('981',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('982',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['979','980','981'])).

thf('983',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('984',plain,
    ( ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['982','983'])).

thf('985',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('986',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
      = o_0_0_xboole_0 ) ),
    inference(clc,[status(thm)],['984','985'])).

thf('987',plain,
    ( ( sk_D_2 @ sk_C @ sk_B @ sk_A )
    = o_0_0_xboole_0 ),
    inference(clc,[status(thm)],['976','986'])).

thf('988',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( zip_tseitin_8 @ X1 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( zip_tseitin_2 @ ( sk_D_2 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ X0 @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','780','786'])).

thf('989',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ o_0_0_xboole_0 @ sk_C @ sk_B @ sk_A )
      | ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['987','988'])).

thf('990',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( zip_tseitin_2 @ o_0_0_xboole_0 @ X1 @ X2 @ X0 ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('991',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('992',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_4 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['989','990','991'])).

thf('993',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','992'])).

thf('994',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','993'])).

thf('995',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('996',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','993'])).

thf('997',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ~ ( zip_tseitin_3 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_13])).

thf('998',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['996','997'])).

thf('999',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('1000',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['998','999'])).

thf('1001',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['995','1000'])).

thf('1002',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['1001'])).

thf('1003',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1004',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['1002','1003'])).

thf('1005',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1006',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['1004','1005'])).

thf('1007',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['996','997'])).

thf('1008',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('1009',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1007','1008'])).

thf('1010',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['1006','1009'])).

thf('1011',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(simplify,[status(thm)],['1010'])).

thf('1012',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1013',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['1011','1012'])).

thf('1014',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1015',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['1013','1014'])).

thf('1016',plain,
    ( ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['1004','1005'])).

thf('1017',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('1018',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1016','1017'])).

thf('1019',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1020',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1021',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['1018','1019','1020'])).

thf('1022',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1023',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['1021','1022'])).

thf('1024',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1025',plain,
    ( ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ) ),
    inference(clc,[status(thm)],['1023','1024'])).

thf('1026',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['1015','1025'])).

thf('1027',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('1028',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1026','1027'])).

thf('1029',plain,(
    ! [X40: $i] :
      ( ( m1_subset_1 @ ( sk_E @ X40 ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1030',plain,
    ( ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1028','1029'])).

thf('1031',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['1015','1025'])).

thf('1032',plain,(
    m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['1030','1031'])).

thf('1033',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1026','1027'])).

thf('1034',plain,(
    ! [X40: $i] :
      ( ( X40
        = ( k1_yellow_0 @ sk_A @ ( sk_E @ X40 ) ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1035',plain,
    ( ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
      = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1033','1034'])).

thf('1036',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['1015','1025'])).

thf('1037',plain,
    ( ( sk_D_1 @ sk_C @ sk_B @ sk_A )
    = ( k1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['1035','1036'])).

thf('1038',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( zip_tseitin_3 @ ( k1_yellow_0 @ X18 @ X19 ) @ X16 @ X17 @ X18 )
      | ~ ( r1_yellow_0 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( v1_finset_1 @ X19 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('1039',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['1037','1038'])).

thf('1040',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1026','1027'])).

thf('1041',plain,(
    ! [X40: $i] :
      ( ( v1_finset_1 @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1042',plain,
    ( ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1040','1041'])).

thf('1043',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['1015','1025'])).

thf('1044',plain,(
    v1_finset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['1042','1043'])).

thf('1045',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1026','1027'])).

thf('1046',plain,(
    ! [X40: $i] :
      ( ( r1_yellow_0 @ sk_A @ ( sk_E @ X40 ) )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1047',plain,
    ( ~ ( r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C )
    | ( r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1045','1046'])).

thf('1048',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ sk_C ),
    inference(clc,[status(thm)],['1015','1025'])).

thf('1049',plain,(
    r1_yellow_0 @ sk_A @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['1047','1048'])).

thf('1050',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_E @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['1039','1044','1049'])).

thf('1051',plain,(
    ! [X0: $i] :
      ~ ( zip_tseitin_3 @ ( sk_D_1 @ sk_C @ sk_B @ sk_A ) @ X0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['1032','1050'])).

thf('1052',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A )
      | ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['994','1051'])).

thf('1053',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1054',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['1052','1053'])).

thf('1055',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('1056',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1054','1055'])).

thf('1057',plain,
    ( ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','1056'])).

thf('1058',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(simplify,[status(thm)],['1057'])).

thf('1059',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1060',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['1058','1059'])).

thf('1061',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1062',plain,(
    r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['1060','1061'])).

thf('1063',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_yellow_0 @ X0 @ X2 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( r2_lattice3 @ X0 @ X2 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r2_lattice3 @ X0 @ X1 @ ( sk_D @ X1 @ X2 @ X0 ) )
      | ~ ( r1_yellow_0 @ X0 @ X2 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t47_yellow_0])).

thf('1064',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( r1_yellow_0 @ sk_A @ sk_B )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1062','1063'])).

thf('1065',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1066',plain,(
    r1_yellow_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1067',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['1064','1065','1066'])).

thf('1068',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1069',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['1067','1068'])).

thf('1070',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1071',plain,(
    ~ ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['1069','1070'])).

thf('1072',plain,(
    r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['1060','1061'])).

thf('1073',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( zip_tseitin_8 @ ( sk_D @ X0 @ sk_B @ sk_A ) @ sk_C @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['1052','1053'])).

thf('1074',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_lattice3 @ X31 @ X34 @ X33 )
      | ( r2_lattice3 @ X31 @ X32 @ X33 )
      | ~ ( zip_tseitin_8 @ X33 @ X32 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('1075',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_A @ sk_B )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r2_lattice3 @ sk_A @ sk_B @ ( sk_D @ X0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1073','1074'])).

thf('1076',plain,
    ( ( r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( ( k1_yellow_0 @ sk_A @ sk_B )
      = ( k1_yellow_0 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1072','1075'])).

thf('1077',plain,(
    ( k1_yellow_0 @ sk_A @ sk_C )
 != ( k1_yellow_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1078',plain,(
    r2_lattice3 @ sk_A @ sk_C @ ( sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['1076','1077'])).

thf('1079',plain,(
    $false ),
    inference(demod,[status(thm)],['1071','1078'])).


%------------------------------------------------------------------------------
