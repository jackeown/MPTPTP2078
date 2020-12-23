%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4rmF04srDk

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 420 expanded)
%              Number of leaves         :   33 ( 141 expanded)
%              Depth                    :   20
%              Number of atoms          :  865 (5410 expanded)
%              Number of equality atoms :   15 ( 198 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(t60_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k3_orders_2 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_orders_2])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('15',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ( k3_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('18',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('19',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X8: $i] :
      ( ( ( k1_struct_0 @ X8 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('21',plain,
    ( ( k1_struct_0 @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','21'])).

thf('23',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t57_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) )
                  <=> ( ( r2_orders_2 @ A @ B @ C )
                      & ( r2_hidden @ B @ D ) ) ) ) ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( r2_hidden @ X21 @ ( k3_orders_2 @ X22 @ X23 @ X24 ) )
      | ( r2_hidden @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t57_orders_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ X2 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    m1_subset_1 @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('30',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['16','21'])).

thf('32',plain,(
    m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['27','32','33','34','35','36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(t46_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) )
        = k1_xboole_0 ) ) )).

thf('47',plain,(
    ! [X17: $i] :
      ( ( ( k2_orders_2 @ X17 @ ( k2_struct_0 @ X17 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t46_orders_2])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('48',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(t49_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ~ ( ( r2_hidden @ B @ C )
                  & ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) )).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_hidden @ X18 @ ( k2_orders_2 @ X19 @ X20 ) )
      | ~ ( r2_hidden @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t49_orders_2])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    r2_hidden @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 ),
    inference(clc,[status(thm)],['38','39'])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_C @ ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','56'])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('59',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['62','63'])).

thf(fc5_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) )).

thf('65',plain,(
    ! [X12: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X12 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc5_struct_0])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('68',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.4rmF04srDk
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:59:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.55  % Solved by: fo/fo7.sh
% 0.22/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.55  % done 115 iterations in 0.087s
% 0.22/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.55  % SZS output start Refutation
% 0.22/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.55  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.22/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.55  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.22/0.55  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.55  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.22/0.55  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.22/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.55  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.22/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.55  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.22/0.55  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.22/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.22/0.55  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.22/0.55  thf(t60_orders_2, conjecture,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.55    (~( ![A:$i]:
% 0.22/0.55        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.55            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.55          ( ![B:$i]:
% 0.22/0.55            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.22/0.55    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.22/0.55  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('1', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(t4_subset_1, axiom,
% 0.22/0.55    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.55  thf('3', plain,
% 0.22/0.55      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.55  thf(dt_k3_orders_2, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.22/0.55         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.22/0.55         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55       ( m1_subset_1 @
% 0.22/0.55         ( k3_orders_2 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.55  thf('4', plain,
% 0.22/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.22/0.55          | ~ (l1_orders_2 @ X14)
% 0.22/0.55          | ~ (v5_orders_2 @ X14)
% 0.22/0.55          | ~ (v4_orders_2 @ X14)
% 0.22/0.55          | ~ (v3_orders_2 @ X14)
% 0.22/0.55          | (v2_struct_0 @ X14)
% 0.22/0.55          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.22/0.55          | (m1_subset_1 @ (k3_orders_2 @ X14 @ X13 @ X15) @ 
% 0.22/0.55             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k3_orders_2])).
% 0.22/0.55  thf('5', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1) @ 
% 0.22/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v3_orders_2 @ X0)
% 0.22/0.55          | ~ (v4_orders_2 @ X0)
% 0.22/0.55          | ~ (v5_orders_2 @ X0)
% 0.22/0.55          | ~ (l1_orders_2 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.55  thf('6', plain,
% 0.22/0.55      ((~ (l1_orders_2 @ sk_A)
% 0.22/0.55        | ~ (v5_orders_2 @ sk_A)
% 0.22/0.55        | ~ (v4_orders_2 @ sk_A)
% 0.22/0.55        | ~ (v3_orders_2 @ sk_A)
% 0.22/0.55        | (v2_struct_0 @ sk_A)
% 0.22/0.55        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('sup-', [status(thm)], ['2', '5'])).
% 0.22/0.55  thf('7', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('8', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('9', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('10', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('11', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A)
% 0.22/0.55        | (m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.22/0.55      inference('demod', [status(thm)], ['6', '7', '8', '9', '10'])).
% 0.22/0.55  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('13', plain,
% 0.22/0.55      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['11', '12'])).
% 0.22/0.55  thf(t10_subset_1, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.55       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.55            ( ![C:$i]:
% 0.22/0.55              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.55  thf('14', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.22/0.55          | ((X0) = (k1_xboole_0))
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.22/0.55  thf('15', plain,
% 0.22/0.55      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 0.22/0.55        | (r2_hidden @ 
% 0.22/0.55           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55            (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55           (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.55  thf('16', plain,
% 0.22/0.55      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf(dt_l1_orders_2, axiom,
% 0.22/0.55    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.22/0.55  thf('18', plain,
% 0.22/0.55      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_orders_2 @ X16))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.22/0.55  thf('19', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf(d2_struct_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.55  thf('20', plain,
% 0.22/0.55      (![X8 : $i]:
% 0.22/0.55         (((k1_struct_0 @ X8) = (k1_xboole_0)) | ~ (l1_struct_0 @ X8))),
% 0.22/0.55      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.22/0.55  thf('21', plain, (((k1_struct_0 @ sk_A) = (k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.55  thf('22', plain,
% 0.22/0.55      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['16', '21'])).
% 0.22/0.55  thf('23', plain,
% 0.22/0.55      ((r2_hidden @ 
% 0.22/0.55        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55         (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55        (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['15', '22'])).
% 0.22/0.55  thf('24', plain,
% 0.22/0.55      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.55  thf(t57_orders_2, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55               ( ![D:$i]:
% 0.22/0.55                 ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55                   ( ( r2_hidden @ B @ ( k3_orders_2 @ A @ D @ C ) ) <=>
% 0.22/0.55                     ( ( r2_orders_2 @ A @ B @ C ) & ( r2_hidden @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('25', plain,
% 0.22/0.55      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 0.22/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.22/0.55          | ~ (r2_hidden @ X21 @ (k3_orders_2 @ X22 @ X23 @ X24))
% 0.22/0.55          | (r2_hidden @ X21 @ X23)
% 0.22/0.55          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X22))
% 0.22/0.55          | ~ (l1_orders_2 @ X22)
% 0.22/0.55          | ~ (v5_orders_2 @ X22)
% 0.22/0.55          | ~ (v4_orders_2 @ X22)
% 0.22/0.55          | ~ (v3_orders_2 @ X22)
% 0.22/0.55          | (v2_struct_0 @ X22))),
% 0.22/0.55      inference('cnf', [status(esa)], [t57_orders_2])).
% 0.22/0.55  thf('26', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.55         ((v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v3_orders_2 @ X0)
% 0.22/0.55          | ~ (v4_orders_2 @ X0)
% 0.22/0.55          | ~ (v5_orders_2 @ X0)
% 0.22/0.55          | ~ (l1_orders_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.55          | (r2_hidden @ X2 @ k1_xboole_0)
% 0.22/0.55          | ~ (r2_hidden @ X2 @ (k3_orders_2 @ X0 @ k1_xboole_0 @ X1))
% 0.22/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.55  thf('27', plain,
% 0.22/0.55      ((~ (m1_subset_1 @ 
% 0.22/0.55           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55            (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55           (u1_struct_0 @ sk_A))
% 0.22/0.55        | (r2_hidden @ 
% 0.22/0.55           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55            (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55           k1_xboole_0)
% 0.22/0.55        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.22/0.55        | ~ (l1_orders_2 @ sk_A)
% 0.22/0.55        | ~ (v5_orders_2 @ sk_A)
% 0.22/0.55        | ~ (v4_orders_2 @ sk_A)
% 0.22/0.55        | ~ (v3_orders_2 @ sk_A)
% 0.22/0.55        | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['23', '26'])).
% 0.22/0.55  thf('28', plain,
% 0.22/0.55      ((m1_subset_1 @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('clc', [status(thm)], ['11', '12'])).
% 0.22/0.55  thf('29', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (sk_C @ X0 @ X1) @ X1)
% 0.22/0.55          | ((X0) = (k1_xboole_0))
% 0.22/0.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.22/0.55      inference('cnf', [status(esa)], [t10_subset_1])).
% 0.22/0.55  thf('30', plain,
% 0.22/0.55      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 0.22/0.55        | (m1_subset_1 @ 
% 0.22/0.55           (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55            (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55           (u1_struct_0 @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.55  thf('31', plain,
% 0.22/0.55      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.22/0.55      inference('demod', [status(thm)], ['16', '21'])).
% 0.22/0.55  thf('32', plain,
% 0.22/0.55      ((m1_subset_1 @ 
% 0.22/0.55        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55         (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55        (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('simplify_reflect-', [status(thm)], ['30', '31'])).
% 0.22/0.55  thf('33', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('35', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('36', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('37', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('38', plain,
% 0.22/0.55      (((r2_hidden @ 
% 0.22/0.55         (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55          (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55         k1_xboole_0)
% 0.22/0.55        | (v2_struct_0 @ sk_A))),
% 0.22/0.55      inference('demod', [status(thm)],
% 0.22/0.55                ['27', '32', '33', '34', '35', '36', '37'])).
% 0.22/0.55  thf('39', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('40', plain,
% 0.22/0.55      ((r2_hidden @ 
% 0.22/0.55        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55         (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55        k1_xboole_0)),
% 0.22/0.55      inference('clc', [status(thm)], ['38', '39'])).
% 0.22/0.55  thf('41', plain,
% 0.22/0.55      (![X2 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.55  thf(t4_subset, axiom,
% 0.22/0.55    (![A:$i,B:$i,C:$i]:
% 0.22/0.55     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.55       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.55  thf('42', plain,
% 0.22/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X5 @ X6)
% 0.22/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.22/0.55          | (m1_subset_1 @ X5 @ X7))),
% 0.22/0.55      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.55  thf('43', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.55  thf('44', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (m1_subset_1 @ 
% 0.22/0.55          (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55           (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55          X0)),
% 0.22/0.55      inference('sup-', [status(thm)], ['40', '43'])).
% 0.22/0.55  thf(t2_subset, axiom,
% 0.22/0.55    (![A:$i,B:$i]:
% 0.22/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.22/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.22/0.55  thf('45', plain,
% 0.22/0.55      (![X3 : $i, X4 : $i]:
% 0.22/0.55         ((r2_hidden @ X3 @ X4)
% 0.22/0.55          | (v1_xboole_0 @ X4)
% 0.22/0.55          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.22/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.22/0.55  thf('46', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ X0)
% 0.22/0.55          | (r2_hidden @ 
% 0.22/0.55             (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55              (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55             X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.55  thf(t46_orders_2, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.55       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.55  thf('47', plain,
% 0.22/0.55      (![X17 : $i]:
% 0.22/0.55         (((k2_orders_2 @ X17 @ (k2_struct_0 @ X17)) = (k1_xboole_0))
% 0.22/0.55          | ~ (l1_orders_2 @ X17)
% 0.22/0.55          | ~ (v5_orders_2 @ X17)
% 0.22/0.55          | ~ (v4_orders_2 @ X17)
% 0.22/0.55          | ~ (v3_orders_2 @ X17)
% 0.22/0.55          | (v2_struct_0 @ X17))),
% 0.22/0.55      inference('cnf', [status(esa)], [t46_orders_2])).
% 0.22/0.55  thf(dt_k2_struct_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( l1_struct_0 @ A ) =>
% 0.22/0.55       ( m1_subset_1 @
% 0.22/0.55         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.22/0.55  thf('48', plain,
% 0.22/0.55      (![X11 : $i]:
% 0.22/0.55         ((m1_subset_1 @ (k2_struct_0 @ X11) @ 
% 0.22/0.55           (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.22/0.55          | ~ (l1_struct_0 @ X11))),
% 0.22/0.55      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.22/0.55  thf(t49_orders_2, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.22/0.55         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.22/0.55       ( ![B:$i]:
% 0.22/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.22/0.55           ( ![C:$i]:
% 0.22/0.55             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.22/0.55               ( ~( ( r2_hidden @ B @ C ) & 
% 0.22/0.55                    ( r2_hidden @ B @ ( k2_orders_2 @ A @ C ) ) ) ) ) ) ) ) ))).
% 0.22/0.55  thf('49', plain,
% 0.22/0.55      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.55         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.22/0.55          | ~ (r2_hidden @ X18 @ (k2_orders_2 @ X19 @ X20))
% 0.22/0.55          | ~ (r2_hidden @ X18 @ X20)
% 0.22/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.22/0.55          | ~ (l1_orders_2 @ X19)
% 0.22/0.55          | ~ (v5_orders_2 @ X19)
% 0.22/0.55          | ~ (v4_orders_2 @ X19)
% 0.22/0.55          | ~ (v3_orders_2 @ X19)
% 0.22/0.55          | (v2_struct_0 @ X19))),
% 0.22/0.55      inference('cnf', [status(esa)], [t49_orders_2])).
% 0.22/0.55  thf('50', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (l1_struct_0 @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v3_orders_2 @ X0)
% 0.22/0.55          | ~ (v4_orders_2 @ X0)
% 0.22/0.55          | ~ (v5_orders_2 @ X0)
% 0.22/0.55          | ~ (l1_orders_2 @ X0)
% 0.22/0.55          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 0.22/0.55          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.55  thf('51', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v3_orders_2 @ X0)
% 0.22/0.55          | ~ (v4_orders_2 @ X0)
% 0.22/0.55          | ~ (v5_orders_2 @ X0)
% 0.22/0.55          | ~ (l1_orders_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.55          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 0.22/0.55          | ~ (l1_orders_2 @ X0)
% 0.22/0.55          | ~ (v5_orders_2 @ X0)
% 0.22/0.55          | ~ (v4_orders_2 @ X0)
% 0.22/0.55          | ~ (v3_orders_2 @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (l1_struct_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['47', '50'])).
% 0.22/0.55  thf('52', plain,
% 0.22/0.55      (![X0 : $i, X1 : $i]:
% 0.22/0.55         (~ (l1_struct_0 @ X0)
% 0.22/0.55          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 0.22/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.22/0.55          | ~ (l1_orders_2 @ X0)
% 0.22/0.55          | ~ (v5_orders_2 @ X0)
% 0.22/0.55          | ~ (v4_orders_2 @ X0)
% 0.22/0.55          | ~ (v3_orders_2 @ X0)
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.22/0.55      inference('simplify', [status(thm)], ['51'])).
% 0.22/0.55  thf('53', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.22/0.55          | ~ (r2_hidden @ 
% 0.22/0.55               (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55                (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55               k1_xboole_0)
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v3_orders_2 @ X0)
% 0.22/0.55          | ~ (v4_orders_2 @ X0)
% 0.22/0.55          | ~ (v5_orders_2 @ X0)
% 0.22/0.55          | ~ (l1_orders_2 @ X0)
% 0.22/0.55          | ~ (m1_subset_1 @ 
% 0.22/0.55               (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55                (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55               (u1_struct_0 @ X0))
% 0.22/0.55          | ~ (l1_struct_0 @ X0))),
% 0.22/0.55      inference('sup-', [status(thm)], ['46', '52'])).
% 0.22/0.55  thf('54', plain,
% 0.22/0.55      ((r2_hidden @ 
% 0.22/0.55        (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55         (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55        k1_xboole_0)),
% 0.22/0.55      inference('clc', [status(thm)], ['38', '39'])).
% 0.22/0.55  thf('55', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         (m1_subset_1 @ 
% 0.22/0.55          (sk_C @ (k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) @ 
% 0.22/0.55           (u1_struct_0 @ sk_A)) @ 
% 0.22/0.55          X0)),
% 0.22/0.55      inference('sup-', [status(thm)], ['40', '43'])).
% 0.22/0.55  thf('56', plain,
% 0.22/0.55      (![X0 : $i]:
% 0.22/0.55         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.22/0.55          | (v2_struct_0 @ X0)
% 0.22/0.55          | ~ (v3_orders_2 @ X0)
% 0.22/0.55          | ~ (v4_orders_2 @ X0)
% 0.22/0.55          | ~ (v5_orders_2 @ X0)
% 0.22/0.55          | ~ (l1_orders_2 @ X0)
% 0.22/0.55          | ~ (l1_struct_0 @ X0))),
% 0.22/0.55      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.22/0.55  thf('57', plain,
% 0.22/0.55      ((~ (l1_struct_0 @ sk_A)
% 0.22/0.55        | ~ (v5_orders_2 @ sk_A)
% 0.22/0.55        | ~ (v4_orders_2 @ sk_A)
% 0.22/0.55        | ~ (v3_orders_2 @ sk_A)
% 0.22/0.55        | (v2_struct_0 @ sk_A)
% 0.22/0.55        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('sup-', [status(thm)], ['1', '56'])).
% 0.22/0.55  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf('59', plain, ((v5_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('60', plain, ((v4_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('61', plain, ((v3_orders_2 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('62', plain,
% 0.22/0.55      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.22/0.55      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.22/0.55  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.55  thf('64', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.22/0.55      inference('clc', [status(thm)], ['62', '63'])).
% 0.22/0.55  thf(fc5_struct_0, axiom,
% 0.22/0.55    (![A:$i]:
% 0.22/0.55     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.55       ( ~( v1_xboole_0 @ ( k2_struct_0 @ A ) ) ) ))).
% 0.22/0.55  thf('65', plain,
% 0.22/0.55      (![X12 : $i]:
% 0.22/0.55         (~ (v1_xboole_0 @ (k2_struct_0 @ X12))
% 0.22/0.55          | ~ (l1_struct_0 @ X12)
% 0.22/0.55          | (v2_struct_0 @ X12))),
% 0.22/0.55      inference('cnf', [status(esa)], [fc5_struct_0])).
% 0.22/0.55  thf('66', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.22/0.55      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.55  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.55  thf('68', plain, ((v2_struct_0 @ sk_A)),
% 0.22/0.55      inference('demod', [status(thm)], ['66', '67'])).
% 0.22/0.55  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 0.22/0.55  
% 0.22/0.55  % SZS output end Refutation
% 0.22/0.55  
% 0.22/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
