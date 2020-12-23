%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CHuKXGbc8i

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 293 expanded)
%              Number of leaves         :   35 ( 104 expanded)
%              Depth                    :   16
%              Number of atoms          :  845 (3598 expanded)
%              Number of equality atoms :   39 ( 189 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(t87_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
           != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
           => ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) )
             != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_orders_2])).

thf('0',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ~ ( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_orders_1 @ X16 @ ( k1_orders_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fc9_orders_2])).

thf('2',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('12',plain,
    ( ( k3_tarski @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_orders_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( ( k3_tarski @ A )
           != k1_xboole_0 )
          & ! [B: $i] :
              ~ ( ( B != k1_xboole_0 )
                & ( r2_hidden @ B @ A ) ) )
      & ~ ( ? [B: $i] :
              ( ( r2_hidden @ B @ A )
              & ( B != k1_xboole_0 ) )
          & ( ( k3_tarski @ A )
            = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17 = k1_xboole_0 )
      | ~ ( r2_hidden @ X17 @ X18 )
      | ( ( k3_tarski @ X18 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t91_orders_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( ( sk_B @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('18',plain,
    ( ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
    | ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( r2_hidden @ k1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( C
                = ( k4_orders_2 @ A @ B ) )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ C )
                <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) )).

thf('21',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( m1_orders_1 @ X6 @ ( k1_orders_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( X8
       != ( k4_orders_2 @ X7 @ X6 ) )
      | ( m2_orders_2 @ X10 @ X7 @ X6 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('22',plain,(
    ! [X6: $i,X7: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v3_orders_2 @ X7 )
      | ~ ( v4_orders_2 @ X7 )
      | ~ ( v5_orders_2 @ X7 )
      | ~ ( l1_orders_2 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k4_orders_2 @ X7 @ X6 ) )
      | ( m2_orders_2 @ X10 @ X7 @ X6 )
      | ~ ( m1_orders_1 @ X6 @ ( k1_orders_1 @ ( u1_struct_0 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) )
      | ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) )
     => ! [C: $i] :
          ( ( m2_orders_2 @ C @ A @ B )
         => ( ( v6_orders_2 @ C @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m2_orders_2 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(d16_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( ( v6_orders_2 @ C @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
             => ( ( m2_orders_2 @ C @ A @ B )
              <=> ( ( C != k1_xboole_0 )
                  & ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                     => ( ( r2_hidden @ D @ C )
                       => ( ( k1_funct_1 @ B @ ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) )
                          = D ) ) ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_orders_1 @ X2 @ ( k1_orders_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m2_orders_2 @ X4 @ X3 @ X2 )
      | ( X4 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( v6_orders_2 @ X4 @ X3 )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 )
      | ~ ( v4_orders_2 @ X3 )
      | ~ ( v3_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d16_orders_2])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v3_orders_2 @ X3 )
      | ~ ( v4_orders_2 @ X3 )
      | ~ ( v5_orders_2 @ X3 )
      | ~ ( l1_orders_2 @ X3 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X3 @ X2 )
      | ~ ( m1_orders_1 @ X2 @ ( k1_orders_1 @ ( u1_struct_0 @ X3 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( m1_orders_1 @ X2 @ ( k1_orders_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X1 @ X2 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( v5_orders_2 @ X1 )
      | ~ ( v4_orders_2 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('53',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_orders_1 @ X13 @ ( k1_orders_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v6_orders_2 @ X14 @ X12 )
      | ~ ( m2_orders_2 @ X14 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ X0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( v6_orders_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['52','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('65',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v6_orders_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('66',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('67',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('69',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['66','69'])).

thf('71',plain,(
    v6_orders_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['65','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['66','69'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
        = k1_xboole_0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['47','48','49','50','51','71','72'])).

thf('74',plain,
    ( ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 )
    | ( v2_struct_0 @ sk_A )
    | ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','73'])).

thf('75',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('76',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( k4_orders_2 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['66','69'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['9','78','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CHuKXGbc8i
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:07:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 171 iterations in 0.099s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.21/0.56  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.56  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.21/0.56  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.56  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.21/0.56  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.56  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.21/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.56  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.21/0.56  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.56  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.56  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.21/0.56  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.21/0.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.56  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.21/0.56  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.56  thf(t87_orders_2, conjecture,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i]:
% 0.21/0.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56          ( ![B:$i]:
% 0.21/0.56            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(fc9_orders_2, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.56         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.56       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (![X15 : $i, X16 : $i]:
% 0.21/0.56         (~ (l1_orders_2 @ X15)
% 0.21/0.56          | ~ (v5_orders_2 @ X15)
% 0.21/0.56          | ~ (v4_orders_2 @ X15)
% 0.21/0.56          | ~ (v3_orders_2 @ X15)
% 0.21/0.56          | (v2_struct_0 @ X15)
% 0.21/0.56          | ~ (m1_orders_1 @ X16 @ (k1_orders_1 @ (u1_struct_0 @ X15)))
% 0.21/0.56          | ~ (v1_xboole_0 @ (k4_orders_2 @ X15 @ X16)))),
% 0.21/0.56      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.56        | (v2_struct_0 @ sk_A)
% 0.21/0.56        | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56        | ~ (v4_orders_2 @ sk_A)
% 0.21/0.56        | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56        | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.56  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.21/0.56  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('9', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))),
% 0.21/0.56      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t7_xboole_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t91_orders_1, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56            ( ![B:$i]:
% 0.21/0.56              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.21/0.56       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.56            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i]:
% 0.21/0.56         (((X17) = (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ X17 @ X18)
% 0.21/0.56          | ((k3_tarski @ X18) != (k1_xboole_0)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.56          | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((X0) = (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.56        | ((sk_B @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X1 : $i]: (((X1) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X1) @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.56        | ((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.56        | ((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup+', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.56        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d17_orders_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.21/0.56               ( ![D:$i]:
% 0.21/0.56                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.21/0.56         (~ (m1_orders_1 @ X6 @ (k1_orders_1 @ (u1_struct_0 @ X7)))
% 0.21/0.56          | ((X8) != (k4_orders_2 @ X7 @ X6))
% 0.21/0.56          | (m2_orders_2 @ X10 @ X7 @ X6)
% 0.21/0.56          | ~ (r2_hidden @ X10 @ X8)
% 0.21/0.56          | ~ (l1_orders_2 @ X7)
% 0.21/0.56          | ~ (v5_orders_2 @ X7)
% 0.21/0.56          | ~ (v4_orders_2 @ X7)
% 0.21/0.56          | ~ (v3_orders_2 @ X7)
% 0.21/0.56          | (v2_struct_0 @ X7))),
% 0.21/0.56      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i, X10 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X7)
% 0.21/0.56          | ~ (v3_orders_2 @ X7)
% 0.21/0.56          | ~ (v4_orders_2 @ X7)
% 0.21/0.56          | ~ (v5_orders_2 @ X7)
% 0.21/0.56          | ~ (l1_orders_2 @ X7)
% 0.21/0.56          | ~ (r2_hidden @ X10 @ (k4_orders_2 @ X7 @ X6))
% 0.21/0.56          | (m2_orders_2 @ X10 @ X7 @ X6)
% 0.21/0.56          | ~ (m1_orders_1 @ X6 @ (k1_orders_1 @ (u1_struct_0 @ X7))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '22'])).
% 0.21/0.56  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('25', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('26', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('27', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.21/0.56          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.21/0.56  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.21/0.56          | (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.21/0.56      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.56        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['19', '30'])).
% 0.21/0.56  thf('32', plain,
% 0.21/0.56      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(dt_m2_orders_2, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.21/0.56         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.56       ( ![C:$i]:
% 0.21/0.56         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.21/0.56           ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.56             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.21/0.56  thf('33', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.56         (~ (l1_orders_2 @ X12)
% 0.21/0.56          | ~ (v5_orders_2 @ X12)
% 0.21/0.56          | ~ (v4_orders_2 @ X12)
% 0.21/0.56          | ~ (v3_orders_2 @ X12)
% 0.21/0.56          | (v2_struct_0 @ X12)
% 0.21/0.56          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X12)))
% 0.21/0.56          | (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.21/0.56          | ~ (m2_orders_2 @ X14 @ X12 @ X13))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.21/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.56  thf('35', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('36', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('37', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('39', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.21/0.56          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.21/0.56  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('41', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.21/0.56      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.56  thf('42', plain,
% 0.21/0.56      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.56        | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('sup-', [status(thm)], ['31', '41'])).
% 0.21/0.56  thf(l13_xboole_0, axiom,
% 0.21/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.56  thf('43', plain,
% 0.21/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.56  thf(d16_orders_2, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.56         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.21/0.56       ( ![B:$i]:
% 0.21/0.56         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.56           ( ![C:$i]:
% 0.21/0.56             ( ( ( v6_orders_2 @ C @ A ) & 
% 0.21/0.56                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.21/0.56               ( ( m2_orders_2 @ C @ A @ B ) <=>
% 0.21/0.56                 ( ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56                   ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C ) & 
% 0.21/0.56                   ( ![D:$i]:
% 0.21/0.56                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.56                       ( ( r2_hidden @ D @ C ) =>
% 0.21/0.56                         ( ( k1_funct_1 @
% 0.21/0.56                             B @ 
% 0.21/0.56                             ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) ) =
% 0.21/0.56                           ( D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.56  thf('44', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.56         (~ (m1_orders_1 @ X2 @ (k1_orders_1 @ (u1_struct_0 @ X3)))
% 0.21/0.56          | ~ (m2_orders_2 @ X4 @ X3 @ X2)
% 0.21/0.56          | ((X4) != (k1_xboole_0))
% 0.21/0.56          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.21/0.56          | ~ (v6_orders_2 @ X4 @ X3)
% 0.21/0.56          | ~ (l1_orders_2 @ X3)
% 0.21/0.56          | ~ (v5_orders_2 @ X3)
% 0.21/0.56          | ~ (v4_orders_2 @ X3)
% 0.21/0.56          | ~ (v3_orders_2 @ X3)
% 0.21/0.56          | (v2_struct_0 @ X3))),
% 0.21/0.56      inference('cnf', [status(esa)], [d16_orders_2])).
% 0.21/0.56  thf('45', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i]:
% 0.21/0.56         ((v2_struct_0 @ X3)
% 0.21/0.56          | ~ (v3_orders_2 @ X3)
% 0.21/0.56          | ~ (v4_orders_2 @ X3)
% 0.21/0.56          | ~ (v5_orders_2 @ X3)
% 0.21/0.56          | ~ (l1_orders_2 @ X3)
% 0.21/0.56          | ~ (v6_orders_2 @ k1_xboole_0 @ X3)
% 0.21/0.56          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X3)))
% 0.21/0.56          | ~ (m2_orders_2 @ k1_xboole_0 @ X3 @ X2)
% 0.21/0.56          | ~ (m1_orders_1 @ X2 @ (k1_orders_1 @ (u1_struct_0 @ X3))))),
% 0.21/0.56      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.56  thf('46', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X1)))
% 0.21/0.56          | ~ (v1_xboole_0 @ X0)
% 0.21/0.56          | ~ (m1_orders_1 @ X2 @ (k1_orders_1 @ (u1_struct_0 @ X1)))
% 0.21/0.56          | ~ (m2_orders_2 @ k1_xboole_0 @ X1 @ X2)
% 0.21/0.56          | ~ (v6_orders_2 @ k1_xboole_0 @ X1)
% 0.21/0.56          | ~ (l1_orders_2 @ X1)
% 0.21/0.56          | ~ (v5_orders_2 @ X1)
% 0.21/0.56          | ~ (v4_orders_2 @ X1)
% 0.21/0.56          | ~ (v3_orders_2 @ X1)
% 0.21/0.56          | (v2_struct_0 @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['43', '45'])).
% 0.21/0.56  thf('47', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.21/0.56          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.56          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.21/0.56          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['42', '46'])).
% 0.21/0.56  thf('48', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('49', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('50', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('52', plain,
% 0.21/0.56      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.56        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['19', '30'])).
% 0.21/0.56  thf('53', plain,
% 0.21/0.56      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('54', plain,
% 0.21/0.56      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.56         (~ (l1_orders_2 @ X12)
% 0.21/0.56          | ~ (v5_orders_2 @ X12)
% 0.21/0.56          | ~ (v4_orders_2 @ X12)
% 0.21/0.56          | ~ (v3_orders_2 @ X12)
% 0.21/0.56          | (v2_struct_0 @ X12)
% 0.21/0.56          | ~ (m1_orders_1 @ X13 @ (k1_orders_1 @ (u1_struct_0 @ X12)))
% 0.21/0.56          | (v6_orders_2 @ X14 @ X12)
% 0.21/0.56          | ~ (m2_orders_2 @ X14 @ X12 @ X13))),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.21/0.56  thf('55', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.21/0.56          | (v6_orders_2 @ X0 @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (v3_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v4_orders_2 @ sk_A)
% 0.21/0.56          | ~ (v5_orders_2 @ sk_A)
% 0.21/0.56          | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.56  thf('56', plain, ((v3_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('57', plain, ((v4_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('58', plain, ((v5_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('60', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.21/0.56          | (v6_orders_2 @ X0 @ sk_A)
% 0.21/0.56          | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.21/0.56  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('62', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((v6_orders_2 @ X0 @ sk_A) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.21/0.56      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.56  thf('63', plain,
% 0.21/0.56      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.56        | (v6_orders_2 @ k1_xboole_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['52', '62'])).
% 0.21/0.56  thf('64', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))),
% 0.21/0.56      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.56  thf('65', plain,
% 0.21/0.56      ((~ (v1_xboole_0 @ k1_xboole_0) | (v6_orders_2 @ k1_xboole_0 @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.56  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.21/0.56  thf('66', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.21/0.56  thf('67', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.21/0.56      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.21/0.56  thf('68', plain,
% 0.21/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.56  thf('69', plain, (((o_0_0_xboole_0) = (k1_xboole_0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.56  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('demod', [status(thm)], ['66', '69'])).
% 0.21/0.56  thf('71', plain, ((v6_orders_2 @ k1_xboole_0 @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['65', '70'])).
% 0.21/0.56  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('demod', [status(thm)], ['66', '69'])).
% 0.21/0.56  thf('73', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.56          | (v2_struct_0 @ sk_A)
% 0.21/0.56          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.21/0.56          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A))))),
% 0.21/0.56      inference('demod', [status(thm)],
% 0.21/0.56                ['47', '48', '49', '50', '51', '71', '72'])).
% 0.21/0.56  thf('74', plain,
% 0.21/0.56      ((~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2)
% 0.21/0.56        | (v2_struct_0 @ sk_A)
% 0.21/0.56        | ((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '73'])).
% 0.21/0.56  thf('75', plain,
% 0.21/0.56      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.21/0.56        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['19', '30'])).
% 0.21/0.56  thf('76', plain,
% 0.21/0.56      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 0.21/0.56      inference('clc', [status(thm)], ['74', '75'])).
% 0.21/0.56  thf('77', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('78', plain, (((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.21/0.56      inference('clc', [status(thm)], ['76', '77'])).
% 0.21/0.56  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.56      inference('demod', [status(thm)], ['66', '69'])).
% 0.21/0.56  thf('80', plain, ($false),
% 0.21/0.56      inference('demod', [status(thm)], ['9', '78', '79'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
