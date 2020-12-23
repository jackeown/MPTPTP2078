%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.unPKgADVV2

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 270 expanded)
%              Number of leaves         :   34 (  96 expanded)
%              Depth                    :   16
%              Number of atoms          :  803 (3564 expanded)
%              Number of equality atoms :   36 ( 184 expanded)
%              Maximal formula depth    :   19 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_orders_1_type,type,(
    m1_orders_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(m2_orders_2_type,type,(
    m2_orders_2: $i > $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k4_orders_2_type,type,(
    k4_orders_2: $i > $i > $i )).

thf(r2_wellord1_type,type,(
    r2_wellord1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_orders_1_type,type,(
    k1_orders_1: $i > $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_orders_1 @ X17 @ ( k1_orders_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_xboole_0 @ ( k4_orders_2 @ X16 @ X17 ) ) ) ),
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

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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
    ! [X18: $i,X19: $i] :
      ( ( X18 = k1_xboole_0 )
      | ~ ( r2_hidden @ X18 @ X19 )
      | ( ( k3_tarski @ X19 )
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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
    ! [X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( m1_orders_1 @ X7 @ ( k1_orders_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( X9
       != ( k4_orders_2 @ X8 @ X7 ) )
      | ( m2_orders_2 @ X11 @ X8 @ X7 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d17_orders_2])).

thf('22',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k4_orders_2 @ X8 @ X7 ) )
      | ( m2_orders_2 @ X11 @ X8 @ X7 )
      | ~ ( m1_orders_1 @ X7 @ ( k1_orders_1 @ ( u1_struct_0 @ X8 ) ) ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_orders_1 @ X14 @ ( k1_orders_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m2_orders_2 @ X15 @ X13 @ X14 ) ) ),
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

thf('43',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_orders_1 @ X3 @ ( k1_orders_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m2_orders_2 @ X5 @ X4 @ X3 )
      | ( X5 != k1_xboole_0 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( v6_orders_2 @ X5 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d16_orders_2])).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ~ ( v5_orders_2 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ X4 @ X3 )
      | ~ ( m1_orders_1 @ X3 @ ( k1_orders_1 @ ( u1_struct_0 @ X4 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
        = k1_xboole_0 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ~ ( v6_orders_2 @ k1_xboole_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('47',plain,(
    m1_orders_1 @ sk_B_2 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_orders_1 @ X14 @ ( k1_orders_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v6_orders_2 @ X15 @ X13 )
      | ~ ( m2_orders_2 @ X15 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_orders_2])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 )
      | ( v6_orders_2 @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v6_orders_2 @ X0 @ sk_A )
      | ~ ( m2_orders_2 @ X0 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( v6_orders_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ ( k4_orders_2 @ sk_A @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('59',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v6_orders_2 @ k1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('61',plain,(
    v6_orders_2 @ k1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
        = k1_xboole_0 )
      | ~ ( m1_orders_1 @ X0 @ ( k1_orders_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','61','62','63','64','65'])).

thf('67',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 )
    | ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ~ ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k4_orders_2 @ sk_A @ sk_B_2 )
      = k1_xboole_0 )
    | ( m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('71',plain,
    ( ( k4_orders_2 @ sk_A @ sk_B_2 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['9','71','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.unPKgADVV2
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:31:54 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.44  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.44  % Solved by: fo/fo7.sh
% 0.19/0.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.44  % done 50 iterations in 0.034s
% 0.19/0.44  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.44  % SZS output start Refutation
% 0.19/0.44  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.44  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.19/0.44  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.19/0.44  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.19/0.44  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.44  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.44  thf(m1_orders_1_type, type, m1_orders_1: $i > $i > $o).
% 0.19/0.44  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.44  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.44  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.44  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.44  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.19/0.44  thf(m2_orders_2_type, type, m2_orders_2: $i > $i > $i > $o).
% 0.19/0.44  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.19/0.44  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.19/0.44  thf(k4_orders_2_type, type, k4_orders_2: $i > $i > $i).
% 0.19/0.44  thf(r2_wellord1_type, type, r2_wellord1: $i > $i > $o).
% 0.19/0.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.44  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.19/0.44  thf(k1_orders_1_type, type, k1_orders_1: $i > $i).
% 0.19/0.44  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.19/0.44  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.44  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.19/0.44  thf(t87_orders_2, conjecture,
% 0.19/0.44    (![A:$i]:
% 0.19/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.44         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.44       ( ![B:$i]:
% 0.19/0.44         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.44           ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.44  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.44    (~( ![A:$i]:
% 0.19/0.44        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.44            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.44          ( ![B:$i]:
% 0.19/0.44            ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.44              ( ( k3_tarski @ ( k4_orders_2 @ A @ B ) ) != ( k1_xboole_0 ) ) ) ) ) )),
% 0.19/0.44    inference('cnf.neg', [status(esa)], [t87_orders_2])).
% 0.19/0.44  thf('0', plain,
% 0.19/0.44      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(fc9_orders_2, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.44         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.19/0.44         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.44       ( ~( v1_xboole_0 @ ( k4_orders_2 @ A @ B ) ) ) ))).
% 0.19/0.44  thf('1', plain,
% 0.19/0.44      (![X16 : $i, X17 : $i]:
% 0.19/0.44         (~ (l1_orders_2 @ X16)
% 0.19/0.44          | ~ (v5_orders_2 @ X16)
% 0.19/0.44          | ~ (v4_orders_2 @ X16)
% 0.19/0.44          | ~ (v3_orders_2 @ X16)
% 0.19/0.44          | (v2_struct_0 @ X16)
% 0.19/0.44          | ~ (m1_orders_1 @ X17 @ (k1_orders_1 @ (u1_struct_0 @ X16)))
% 0.19/0.44          | ~ (v1_xboole_0 @ (k4_orders_2 @ X16 @ X17)))),
% 0.19/0.44      inference('cnf', [status(esa)], [fc9_orders_2])).
% 0.19/0.44  thf('2', plain,
% 0.19/0.44      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.19/0.44        | (v2_struct_0 @ sk_A)
% 0.19/0.44        | ~ (v3_orders_2 @ sk_A)
% 0.19/0.44        | ~ (v4_orders_2 @ sk_A)
% 0.19/0.44        | ~ (v5_orders_2 @ sk_A)
% 0.19/0.44        | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.44  thf('3', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('4', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('5', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('7', plain,
% 0.19/0.44      ((~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)) | (v2_struct_0 @ sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.19/0.44  thf('8', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('9', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))),
% 0.19/0.44      inference('clc', [status(thm)], ['7', '8'])).
% 0.19/0.44  thf('10', plain,
% 0.19/0.44      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(t9_mcart_1, axiom,
% 0.19/0.44    (![A:$i]:
% 0.19/0.44     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.44          ( ![B:$i]:
% 0.19/0.44            ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.44                 ( ![C:$i,D:$i]:
% 0.19/0.44                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.19/0.44                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.44  thf('11', plain,
% 0.19/0.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.19/0.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.19/0.44  thf('12', plain,
% 0.19/0.44      (((k3_tarski @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(t91_orders_1, axiom,
% 0.19/0.44    (![A:$i]:
% 0.19/0.44     ( ( ~( ( ( k3_tarski @ A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.44            ( ![B:$i]:
% 0.19/0.44              ( ~( ( ( B ) != ( k1_xboole_0 ) ) & ( r2_hidden @ B @ A ) ) ) ) ) ) & 
% 0.19/0.44       ( ~( ( ?[B:$i]: ( ( r2_hidden @ B @ A ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.44            ( ( k3_tarski @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.19/0.44  thf('13', plain,
% 0.19/0.44      (![X18 : $i, X19 : $i]:
% 0.19/0.44         (((X18) = (k1_xboole_0))
% 0.19/0.44          | ~ (r2_hidden @ X18 @ X19)
% 0.19/0.44          | ((k3_tarski @ X19) != (k1_xboole_0)))),
% 0.19/0.44      inference('cnf', [status(esa)], [t91_orders_1])).
% 0.19/0.44  thf('14', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.44          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.19/0.44          | ((X0) = (k1_xboole_0)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.44  thf('15', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (((X0) = (k1_xboole_0))
% 0.19/0.44          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.19/0.44      inference('simplify', [status(thm)], ['14'])).
% 0.19/0.44  thf('16', plain,
% 0.19/0.44      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.19/0.44        | ((sk_B @ (k4_orders_2 @ sk_A @ sk_B_2)) = (k1_xboole_0)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['11', '15'])).
% 0.19/0.44  thf('17', plain,
% 0.19/0.44      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.19/0.44      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.19/0.44  thf('18', plain,
% 0.19/0.44      (((r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.19/0.44        | ((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.19/0.44        | ((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.19/0.44      inference('sup+', [status(thm)], ['16', '17'])).
% 0.19/0.44  thf('19', plain,
% 0.19/0.44      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.19/0.44        | (r2_hidden @ k1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2)))),
% 0.19/0.44      inference('simplify', [status(thm)], ['18'])).
% 0.19/0.44  thf('20', plain,
% 0.19/0.44      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(d17_orders_2, axiom,
% 0.19/0.44    (![A:$i]:
% 0.19/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.44         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.44       ( ![B:$i]:
% 0.19/0.44         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.44           ( ![C:$i]:
% 0.19/0.44             ( ( ( C ) = ( k4_orders_2 @ A @ B ) ) <=>
% 0.19/0.44               ( ![D:$i]:
% 0.19/0.44                 ( ( r2_hidden @ D @ C ) <=> ( m2_orders_2 @ D @ A @ B ) ) ) ) ) ) ) ))).
% 0.19/0.44  thf('21', plain,
% 0.19/0.44      (![X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.19/0.44         (~ (m1_orders_1 @ X7 @ (k1_orders_1 @ (u1_struct_0 @ X8)))
% 0.19/0.44          | ((X9) != (k4_orders_2 @ X8 @ X7))
% 0.19/0.44          | (m2_orders_2 @ X11 @ X8 @ X7)
% 0.19/0.44          | ~ (r2_hidden @ X11 @ X9)
% 0.19/0.44          | ~ (l1_orders_2 @ X8)
% 0.19/0.44          | ~ (v5_orders_2 @ X8)
% 0.19/0.44          | ~ (v4_orders_2 @ X8)
% 0.19/0.44          | ~ (v3_orders_2 @ X8)
% 0.19/0.44          | (v2_struct_0 @ X8))),
% 0.19/0.44      inference('cnf', [status(esa)], [d17_orders_2])).
% 0.19/0.44  thf('22', plain,
% 0.19/0.44      (![X7 : $i, X8 : $i, X11 : $i]:
% 0.19/0.44         ((v2_struct_0 @ X8)
% 0.19/0.44          | ~ (v3_orders_2 @ X8)
% 0.19/0.44          | ~ (v4_orders_2 @ X8)
% 0.19/0.44          | ~ (v5_orders_2 @ X8)
% 0.19/0.44          | ~ (l1_orders_2 @ X8)
% 0.19/0.44          | ~ (r2_hidden @ X11 @ (k4_orders_2 @ X8 @ X7))
% 0.19/0.44          | (m2_orders_2 @ X11 @ X8 @ X7)
% 0.19/0.44          | ~ (m1_orders_1 @ X7 @ (k1_orders_1 @ (u1_struct_0 @ X8))))),
% 0.19/0.44      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.44  thf('23', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.19/0.44          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.19/0.44          | ~ (l1_orders_2 @ sk_A)
% 0.19/0.44          | ~ (v5_orders_2 @ sk_A)
% 0.19/0.44          | ~ (v4_orders_2 @ sk_A)
% 0.19/0.44          | ~ (v3_orders_2 @ sk_A)
% 0.19/0.44          | (v2_struct_0 @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['20', '22'])).
% 0.19/0.44  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('25', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('26', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('27', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('28', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         ((m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.19/0.44          | ~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.19/0.44          | (v2_struct_0 @ sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.19/0.44  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('30', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (~ (r2_hidden @ X0 @ (k4_orders_2 @ sk_A @ sk_B_2))
% 0.19/0.44          | (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.19/0.44      inference('clc', [status(thm)], ['28', '29'])).
% 0.19/0.44  thf('31', plain,
% 0.19/0.44      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.19/0.44        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.19/0.44      inference('sup-', [status(thm)], ['19', '30'])).
% 0.19/0.44  thf('32', plain,
% 0.19/0.44      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf(dt_m2_orders_2, axiom,
% 0.19/0.44    (![A:$i,B:$i]:
% 0.19/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.44         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.19/0.44         ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.44       ( ![C:$i]:
% 0.19/0.44         ( ( m2_orders_2 @ C @ A @ B ) =>
% 0.19/0.44           ( ( v6_orders_2 @ C @ A ) & 
% 0.19/0.44             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.19/0.44  thf('33', plain,
% 0.19/0.44      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.44         (~ (l1_orders_2 @ X13)
% 0.19/0.44          | ~ (v5_orders_2 @ X13)
% 0.19/0.44          | ~ (v4_orders_2 @ X13)
% 0.19/0.44          | ~ (v3_orders_2 @ X13)
% 0.19/0.44          | (v2_struct_0 @ X13)
% 0.19/0.44          | ~ (m1_orders_1 @ X14 @ (k1_orders_1 @ (u1_struct_0 @ X13)))
% 0.19/0.44          | (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.19/0.44          | ~ (m2_orders_2 @ X15 @ X13 @ X14))),
% 0.19/0.44      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.19/0.44  thf('34', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.19/0.44          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.44          | (v2_struct_0 @ sk_A)
% 0.19/0.44          | ~ (v3_orders_2 @ sk_A)
% 0.19/0.44          | ~ (v4_orders_2 @ sk_A)
% 0.19/0.44          | ~ (v5_orders_2 @ sk_A)
% 0.19/0.44          | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.44  thf('35', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('36', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('37', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('38', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('39', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.19/0.44          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.44          | (v2_struct_0 @ sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['34', '35', '36', '37', '38'])).
% 0.19/0.44  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('41', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.44          | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.19/0.44      inference('clc', [status(thm)], ['39', '40'])).
% 0.19/0.44  thf('42', plain,
% 0.19/0.44      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.19/0.44        | (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.19/0.44      inference('sup-', [status(thm)], ['31', '41'])).
% 0.19/0.44  thf(d16_orders_2, axiom,
% 0.19/0.44    (![A:$i]:
% 0.19/0.44     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.19/0.44         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.19/0.44       ( ![B:$i]:
% 0.19/0.44         ( ( m1_orders_1 @ B @ ( k1_orders_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.19/0.44           ( ![C:$i]:
% 0.19/0.44             ( ( ( v6_orders_2 @ C @ A ) & 
% 0.19/0.44                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.19/0.44               ( ( m2_orders_2 @ C @ A @ B ) <=>
% 0.19/0.44                 ( ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.19/0.44                   ( r2_wellord1 @ ( u1_orders_2 @ A ) @ C ) & 
% 0.19/0.44                   ( ![D:$i]:
% 0.19/0.44                     ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.44                       ( ( r2_hidden @ D @ C ) =>
% 0.19/0.44                         ( ( k1_funct_1 @
% 0.19/0.44                             B @ 
% 0.19/0.44                             ( k1_orders_2 @ A @ ( k3_orders_2 @ A @ C @ D ) ) ) =
% 0.19/0.44                           ( D ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.44  thf('43', plain,
% 0.19/0.44      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.44         (~ (m1_orders_1 @ X3 @ (k1_orders_1 @ (u1_struct_0 @ X4)))
% 0.19/0.44          | ~ (m2_orders_2 @ X5 @ X4 @ X3)
% 0.19/0.44          | ((X5) != (k1_xboole_0))
% 0.19/0.44          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.19/0.44          | ~ (v6_orders_2 @ X5 @ X4)
% 0.19/0.44          | ~ (l1_orders_2 @ X4)
% 0.19/0.44          | ~ (v5_orders_2 @ X4)
% 0.19/0.44          | ~ (v4_orders_2 @ X4)
% 0.19/0.44          | ~ (v3_orders_2 @ X4)
% 0.19/0.44          | (v2_struct_0 @ X4))),
% 0.19/0.44      inference('cnf', [status(esa)], [d16_orders_2])).
% 0.19/0.44  thf('44', plain,
% 0.19/0.44      (![X3 : $i, X4 : $i]:
% 0.19/0.44         ((v2_struct_0 @ X4)
% 0.19/0.44          | ~ (v3_orders_2 @ X4)
% 0.19/0.44          | ~ (v4_orders_2 @ X4)
% 0.19/0.44          | ~ (v5_orders_2 @ X4)
% 0.19/0.44          | ~ (l1_orders_2 @ X4)
% 0.19/0.44          | ~ (v6_orders_2 @ k1_xboole_0 @ X4)
% 0.19/0.44          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.19/0.44          | ~ (m2_orders_2 @ k1_xboole_0 @ X4 @ X3)
% 0.19/0.44          | ~ (m1_orders_1 @ X3 @ (k1_orders_1 @ (u1_struct_0 @ X4))))),
% 0.19/0.44      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.44  thf('45', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.19/0.44          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.44          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.19/0.44          | ~ (v6_orders_2 @ k1_xboole_0 @ sk_A)
% 0.19/0.44          | ~ (l1_orders_2 @ sk_A)
% 0.19/0.44          | ~ (v5_orders_2 @ sk_A)
% 0.19/0.44          | ~ (v4_orders_2 @ sk_A)
% 0.19/0.44          | ~ (v3_orders_2 @ sk_A)
% 0.19/0.44          | (v2_struct_0 @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['42', '44'])).
% 0.19/0.44  thf('46', plain,
% 0.19/0.44      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.19/0.44        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.19/0.44      inference('sup-', [status(thm)], ['19', '30'])).
% 0.19/0.44  thf('47', plain,
% 0.19/0.44      ((m1_orders_1 @ sk_B_2 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('48', plain,
% 0.19/0.44      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.44         (~ (l1_orders_2 @ X13)
% 0.19/0.44          | ~ (v5_orders_2 @ X13)
% 0.19/0.44          | ~ (v4_orders_2 @ X13)
% 0.19/0.44          | ~ (v3_orders_2 @ X13)
% 0.19/0.44          | (v2_struct_0 @ X13)
% 0.19/0.44          | ~ (m1_orders_1 @ X14 @ (k1_orders_1 @ (u1_struct_0 @ X13)))
% 0.19/0.44          | (v6_orders_2 @ X15 @ X13)
% 0.19/0.44          | ~ (m2_orders_2 @ X15 @ X13 @ X14))),
% 0.19/0.44      inference('cnf', [status(esa)], [dt_m2_orders_2])).
% 0.19/0.44  thf('49', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.19/0.44          | (v6_orders_2 @ X0 @ sk_A)
% 0.19/0.44          | (v2_struct_0 @ sk_A)
% 0.19/0.44          | ~ (v3_orders_2 @ sk_A)
% 0.19/0.44          | ~ (v4_orders_2 @ sk_A)
% 0.19/0.44          | ~ (v5_orders_2 @ sk_A)
% 0.19/0.44          | ~ (l1_orders_2 @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.44  thf('50', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('51', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('52', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('53', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('54', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2)
% 0.19/0.44          | (v6_orders_2 @ X0 @ sk_A)
% 0.19/0.44          | (v2_struct_0 @ sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['49', '50', '51', '52', '53'])).
% 0.19/0.44  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('56', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         ((v6_orders_2 @ X0 @ sk_A) | ~ (m2_orders_2 @ X0 @ sk_A @ sk_B_2))),
% 0.19/0.44      inference('clc', [status(thm)], ['54', '55'])).
% 0.19/0.44  thf('57', plain,
% 0.19/0.44      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.19/0.44        | (v6_orders_2 @ k1_xboole_0 @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['46', '56'])).
% 0.19/0.44  thf('58', plain, (~ (v1_xboole_0 @ (k4_orders_2 @ sk_A @ sk_B_2))),
% 0.19/0.44      inference('clc', [status(thm)], ['7', '8'])).
% 0.19/0.44  thf('59', plain,
% 0.19/0.44      ((~ (v1_xboole_0 @ k1_xboole_0) | (v6_orders_2 @ k1_xboole_0 @ sk_A))),
% 0.19/0.44      inference('sup-', [status(thm)], ['57', '58'])).
% 0.19/0.44  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.44  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.44  thf('61', plain, ((v6_orders_2 @ k1_xboole_0 @ sk_A)),
% 0.19/0.44      inference('demod', [status(thm)], ['59', '60'])).
% 0.19/0.44  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('63', plain, ((v5_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('64', plain, ((v4_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('65', plain, ((v3_orders_2 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('66', plain,
% 0.19/0.44      (![X0 : $i]:
% 0.19/0.44         (((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.19/0.44          | ~ (m1_orders_1 @ X0 @ (k1_orders_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.44          | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ X0)
% 0.19/0.44          | (v2_struct_0 @ sk_A))),
% 0.19/0.44      inference('demod', [status(thm)], ['45', '61', '62', '63', '64', '65'])).
% 0.19/0.44  thf('67', plain,
% 0.19/0.44      (((v2_struct_0 @ sk_A)
% 0.19/0.44        | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2)
% 0.19/0.44        | ((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0)))),
% 0.19/0.44      inference('sup-', [status(thm)], ['10', '66'])).
% 0.19/0.44  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.44  thf('69', plain,
% 0.19/0.44      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.19/0.44        | ~ (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.19/0.44      inference('clc', [status(thm)], ['67', '68'])).
% 0.19/0.44  thf('70', plain,
% 0.19/0.44      ((((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))
% 0.19/0.44        | (m2_orders_2 @ k1_xboole_0 @ sk_A @ sk_B_2))),
% 0.19/0.44      inference('sup-', [status(thm)], ['19', '30'])).
% 0.19/0.44  thf('71', plain, (((k4_orders_2 @ sk_A @ sk_B_2) = (k1_xboole_0))),
% 0.19/0.44      inference('clc', [status(thm)], ['69', '70'])).
% 0.19/0.44  thf('72', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.44      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.44  thf('73', plain, ($false),
% 0.19/0.44      inference('demod', [status(thm)], ['9', '71', '72'])).
% 0.19/0.44  
% 0.19/0.44  % SZS output end Refutation
% 0.19/0.44  
% 0.19/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
