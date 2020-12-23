%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8uV7UFu23j

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 695 expanded)
%              Number of leaves         :   29 ( 218 expanded)
%              Depth                    :   29
%              Number of atoms          :  952 (6821 expanded)
%              Number of equality atoms :   56 ( 449 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(r4_wellord1_type,type,(
    r4_wellord1: $i > $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t50_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ~ ( ~ ( r2_xboole_0 @ A @ B )
              & ( A != B )
              & ~ ( r2_xboole_0 @ B @ A ) ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r2_xboole_0 @ X12 @ X11 )
      | ( X12 = X11 )
      | ( r2_xboole_0 @ X11 @ X12 )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t50_ordinal1])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_xboole_0 @ X8 @ X7 )
      | ~ ( v1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X1 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('4',plain,(
    ! [X24: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X24 ) )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t11_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
           => ( A = B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) )
             => ( A = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t11_wellord2])).

thf('5',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v3_ordinal1 @ X11 )
      | ( r2_xboole_0 @ X12 @ X11 )
      | ( X12 = X11 )
      | ( r2_xboole_0 @ X11 @ X12 )
      | ~ ( v3_ordinal1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t50_ordinal1])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X26 ) @ X25 )
        = ( k1_wellord2 @ X25 ) )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t10_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_hidden @ A @ B )
           => ( A
              = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ( X23
        = ( k1_wellord1 @ ( k1_wellord2 @ X22 ) @ X23 ) )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X1 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k1_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 ) )
      | ~ ( v1_ordinal1 @ X1 )
      | ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t57_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
       => ! [B: $i] :
            ~ ( ( r2_hidden @ B @ ( k3_relat_1 @ A ) )
              & ( r4_wellord1 @ A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_wellord1 @ X15 )
      | ~ ( r4_wellord1 @ X15 @ ( k2_wellord1 @ X15 @ ( k1_wellord1 @ X15 @ X16 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k3_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('17',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18
       != ( k1_wellord2 @ X17 ) )
      | ( ( k3_relat_1 @ X18 )
        = X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('19',plain,(
    ! [X17: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X17 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X17 ) )
        = X17 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('21',plain,(
    ! [X17: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k2_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['16','17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ( X0 = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_ordinal1 @ X0 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_ordinal1 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( v3_ordinal1 @ X1 )
      | ( X0 = X1 )
      | ( r2_xboole_0 @ X1 @ X0 )
      | ~ ( v3_ordinal1 @ X0 )
      | ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( v1_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','24'])).

thf('26',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( ( v1_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('30',plain,(
    v1_ordinal1 @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['25','26','27','30'])).

thf('32',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','33'])).

thf('35',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v1_ordinal1 @ sk_B )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','36'])).

thf('38',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_ordinal1 @ sk_B ),
    inference('sup-',[status(thm)],['28','29'])).

thf('41',plain,
    ( ( r2_xboole_0 @ sk_A @ sk_B )
    | ( sk_B = sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['37','38','39','40'])).

thf('42',plain,
    ( ( sk_B = sk_A )
    | ( r2_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['44','45'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
    | ( sk_B = sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ~ ( r1_tarski @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X24: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X24 ) )
      | ~ ( v3_ordinal1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf('52',plain,(
    r2_xboole_0 @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['42','43'])).

thf('53',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v3_ordinal1 @ X7 )
      | ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_xboole_0 @ X8 @ X7 )
      | ~ ( v1_ordinal1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('54',plain,
    ( ~ ( v1_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X6: $i] :
      ( ( v1_ordinal1 @ X6 )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('57',plain,(
    v1_ordinal1 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['54','57','58'])).

thf('60',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v3_ordinal1 @ X22 )
      | ( X23
        = ( k1_wellord1 @ ( k1_wellord2 @ X22 ) @ X23 ) )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( v3_ordinal1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t10_wellord2])).

thf('61',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ( sk_A
      = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ( X1 = X0 )
      | ( r2_xboole_0 @ X0 @ X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X1 )
        = ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v2_wellord1 @ X15 )
      | ~ ( r4_wellord1 @ X15 @ ( k2_wellord1 @ X15 @ ( k1_wellord1 @ X15 @ X16 ) ) )
      | ~ ( r2_hidden @ X16 @ ( k3_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t57_wellord1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 )
        = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ ( k3_relat_1 @ ( k1_wellord2 @ X1 ) ) )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('69',plain,(
    ! [X17: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X17 ) )
      = X17 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r4_wellord1 @ ( k1_wellord2 @ X1 ) @ ( k1_wellord2 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) ) )
      | ~ ( v3_ordinal1 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( r2_xboole_0 @ X1 @ ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 ) )
      | ( ( k1_wellord1 @ ( k1_wellord2 @ X1 ) @ X0 )
        = X1 )
      | ~ ( v3_ordinal1 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v2_wellord1 @ ( k1_wellord2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_ordinal1 @ sk_B )
    | ( ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A )
      = sk_B )
    | ( r2_xboole_0 @ sk_B @ ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) )
    | ~ ( v3_ordinal1 @ ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_A ) @ ( k1_wellord2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r4_wellord1 @ A @ B )
           => ( r4_wellord1 @ B @ A ) ) ) ) )).

thf('73',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r4_wellord1 @ X13 @ X14 )
      | ~ ( r4_wellord1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t50_wellord1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ( r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('76',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('77',plain,(
    r4_wellord1 @ ( k1_wellord2 @ sk_B ) @ ( k1_wellord2 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['54','57','58'])).

thf('79',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('81',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('82',plain,
    ( sk_A
    = ( k1_wellord1 @ ( k1_wellord2 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('83',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( sk_A = sk_B )
    | ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['71','77','78','79','80','81','82','83'])).

thf('85',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v3_ordinal1 @ sk_B )
    | ( r2_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['51','86'])).

thf('88',plain,(
    v3_ordinal1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    r2_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('91',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference(demod,[status(thm)],['50','91'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8uV7UFu23j
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:12:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 69 iterations in 0.027s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.49  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.21/0.49  thf(v2_wellord1_type, type, v2_wellord1: $i > $o).
% 0.21/0.49  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.21/0.49  thf(r4_wellord1_type, type, r4_wellord1: $i > $i > $o).
% 0.21/0.49  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.21/0.49  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(t50_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.49           ( ~( ( ~( r2_xboole_0 @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.21/0.49                ( ~( r2_xboole_0 @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.49  thf('0', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X11)
% 0.21/0.49          | (r2_xboole_0 @ X12 @ X11)
% 0.21/0.49          | ((X12) = (X11))
% 0.21/0.49          | (r2_xboole_0 @ X11 @ X12)
% 0.21/0.49          | ~ (v3_ordinal1 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t50_ordinal1])).
% 0.21/0.49  thf(t21_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_ordinal1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.49           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X7)
% 0.21/0.49          | (r2_hidden @ X8 @ X7)
% 0.21/0.49          | ~ (r2_xboole_0 @ X8 @ X7)
% 0.21/0.49          | ~ (v1_ordinal1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X1)
% 0.21/0.49          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.49          | ((X1) = (X0))
% 0.21/0.49          | ~ (v3_ordinal1 @ X0)
% 0.21/0.49          | ~ (v1_ordinal1 @ X1)
% 0.21/0.49          | (r2_hidden @ X1 @ X0)
% 0.21/0.49          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.49  thf('3', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ X1 @ X0)
% 0.21/0.49          | ~ (v1_ordinal1 @ X1)
% 0.21/0.49          | ~ (v3_ordinal1 @ X0)
% 0.21/0.49          | ((X1) = (X0))
% 0.21/0.49          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.49          | ~ (v3_ordinal1 @ X1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.49  thf(t7_wellord2, axiom,
% 0.21/0.49    (![A:$i]: ( ( v3_ordinal1 @ A ) => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X24 : $i]:
% 0.21/0.49         ((v2_wellord1 @ (k1_wellord2 @ X24)) | ~ (v3_ordinal1 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.21/0.49  thf(t11_wellord2, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.49           ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.21/0.49             ( ( A ) = ( B ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( v3_ordinal1 @ A ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( v3_ordinal1 @ B ) =>
% 0.21/0.49              ( ( r4_wellord1 @ ( k1_wellord2 @ A ) @ ( k1_wellord2 @ B ) ) =>
% 0.21/0.49                ( ( A ) = ( B ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t11_wellord2])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (![X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X11)
% 0.21/0.49          | (r2_xboole_0 @ X12 @ X11)
% 0.21/0.49          | ((X12) = (X11))
% 0.21/0.49          | (r2_xboole_0 @ X11 @ X12)
% 0.21/0.49          | ~ (v3_ordinal1 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [t50_ordinal1])).
% 0.21/0.49  thf(d8_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.21/0.49       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.21/0.49  thf('7', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X1)
% 0.21/0.49          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.49          | ((X1) = (X0))
% 0.21/0.49          | ~ (v3_ordinal1 @ X0)
% 0.21/0.49          | (r1_tarski @ X1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf(t8_wellord2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.21/0.49       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X25 : $i, X26 : $i]:
% 0.21/0.49         (((k2_wellord1 @ (k1_wellord2 @ X26) @ X25) = (k1_wellord2 @ X25))
% 0.21/0.49          | ~ (r1_tarski @ X25 @ X26))),
% 0.21/0.49      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X0)
% 0.21/0.49          | ((X1) = (X0))
% 0.21/0.49          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.49          | ~ (v3_ordinal1 @ X1)
% 0.21/0.49          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ X1 @ X0)
% 0.21/0.49          | ~ (v1_ordinal1 @ X1)
% 0.21/0.49          | ~ (v3_ordinal1 @ X0)
% 0.21/0.49          | ((X1) = (X0))
% 0.21/0.49          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.49          | ~ (v3_ordinal1 @ X1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.49  thf(t10_wellord2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v3_ordinal1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v3_ordinal1 @ B ) =>
% 0.21/0.49           ( ( r2_hidden @ A @ B ) =>
% 0.21/0.49             ( ( A ) = ( k1_wellord1 @ ( k1_wellord2 @ B ) @ A ) ) ) ) ) ))).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X22 : $i, X23 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X22)
% 0.21/0.49          | ((X23) = (k1_wellord1 @ (k1_wellord2 @ X22) @ X23))
% 0.21/0.49          | ~ (r2_hidden @ X23 @ X22)
% 0.21/0.49          | ~ (v3_ordinal1 @ X23))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X1)
% 0.21/0.49          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.49          | ((X1) = (X0))
% 0.21/0.49          | ~ (v3_ordinal1 @ X0)
% 0.21/0.49          | ~ (v1_ordinal1 @ X1)
% 0.21/0.49          | ~ (v3_ordinal1 @ X1)
% 0.21/0.49          | ((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.21/0.49          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (((X1) = (k1_wellord1 @ (k1_wellord2 @ X0) @ X1))
% 0.21/0.49          | ~ (v1_ordinal1 @ X1)
% 0.21/0.49          | ~ (v3_ordinal1 @ X0)
% 0.21/0.49          | ((X1) = (X0))
% 0.21/0.49          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.49          | ~ (v3_ordinal1 @ X1))),
% 0.21/0.49      inference('simplify', [status(thm)], ['13'])).
% 0.21/0.49  thf(t57_wellord1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ( v2_wellord1 @ A ) =>
% 0.21/0.49         ( ![B:$i]:
% 0.21/0.49           ( ~( ( r2_hidden @ B @ ( k3_relat_1 @ A ) ) & 
% 0.21/0.49                ( r4_wellord1 @
% 0.21/0.49                  A @ ( k2_wellord1 @ A @ ( k1_wellord1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (v2_wellord1 @ X15)
% 0.21/0.49          | ~ (r4_wellord1 @ X15 @ 
% 0.21/0.49               (k2_wellord1 @ X15 @ (k1_wellord1 @ X15 @ X16)))
% 0.21/0.49          | ~ (r2_hidden @ X16 @ (k3_relat_1 @ X15))
% 0.21/0.49          | ~ (v1_relat_1 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.21/0.49  thf('16', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.21/0.49             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.49          | ~ (v3_ordinal1 @ X0)
% 0.21/0.49          | (r2_xboole_0 @ X1 @ X0)
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | ~ (v3_ordinal1 @ X1)
% 0.21/0.49          | ~ (v1_ordinal1 @ X0)
% 0.21/0.49          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.21/0.49          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.49  thf('17', plain, (![X21 : $i]: (v1_relat_1 @ (k1_wellord2 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf(d1_wellord2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.21/0.49         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.49           ( ![C:$i,D:$i]:
% 0.21/0.49             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.49               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.49                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (![X17 : $i, X18 : $i]:
% 0.21/0.49         (((X18) != (k1_wellord2 @ X17))
% 0.21/0.49          | ((k3_relat_1 @ X18) = (X17))
% 0.21/0.49          | ~ (v1_relat_1 @ X18))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (![X17 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X17))
% 0.21/0.49          | ((k3_relat_1 @ (k1_wellord2 @ X17)) = (X17)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.49  thf('20', plain, (![X21 : $i]: (v1_relat_1 @ (k1_wellord2 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('21', plain, (![X17 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X17)) = (X17))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.21/0.49             (k2_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.49          | ~ (v3_ordinal1 @ X0)
% 0.21/0.49          | (r2_xboole_0 @ X1 @ X0)
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | ~ (v3_ordinal1 @ X1)
% 0.21/0.49          | ~ (v1_ordinal1 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.49          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['16', '17', '21'])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0))
% 0.21/0.49          | ~ (v3_ordinal1 @ X0)
% 0.21/0.49          | (r2_xboole_0 @ X1 @ X0)
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | ~ (v3_ordinal1 @ X1)
% 0.21/0.49          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.49          | ~ (v1_ordinal1 @ X0)
% 0.21/0.49          | ~ (v3_ordinal1 @ X1)
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | (r2_xboole_0 @ X1 @ X0)
% 0.21/0.49          | ~ (v3_ordinal1 @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['10', '22'])).
% 0.21/0.49  thf('24', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v1_ordinal1 @ X0)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.49          | ~ (v2_wellord1 @ (k1_wellord2 @ X1))
% 0.21/0.49          | ~ (v3_ordinal1 @ X1)
% 0.21/0.49          | ((X0) = (X1))
% 0.21/0.49          | (r2_xboole_0 @ X1 @ X0)
% 0.21/0.49          | ~ (v3_ordinal1 @ X0)
% 0.21/0.49          | ~ (r4_wellord1 @ (k1_wellord2 @ X1) @ (k1_wellord2 @ X0)))),
% 0.21/0.49      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((~ (v3_ordinal1 @ sk_B)
% 0.21/0.49        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.49        | ((sk_B) = (sk_A))
% 0.21/0.49        | ~ (v3_ordinal1 @ sk_A)
% 0.21/0.49        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.21/0.49        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.21/0.49        | ~ (v1_ordinal1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['5', '24'])).
% 0.21/0.49  thf('26', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc1_ordinal1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.21/0.49  thf('29', plain, (![X6 : $i]: ((v1_ordinal1 @ X6) | ~ (v3_ordinal1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.49  thf('30', plain, ((v1_ordinal1 @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('31', plain,
% 0.21/0.49      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.49        | ((sk_B) = (sk_A))
% 0.21/0.49        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.21/0.49        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['25', '26', '27', '30'])).
% 0.21/0.49  thf('32', plain, (((sk_A) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.49        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_A))
% 0.21/0.49        | ~ (r2_hidden @ sk_B @ sk_A))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((~ (v3_ordinal1 @ sk_A)
% 0.21/0.49        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.21/0.49        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['4', '33'])).
% 0.21/0.49  thf('35', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      ((~ (r2_hidden @ sk_B @ sk_A) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      ((~ (v3_ordinal1 @ sk_B)
% 0.21/0.49        | (r2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.49        | ((sk_B) = (sk_A))
% 0.21/0.49        | ~ (v3_ordinal1 @ sk_A)
% 0.21/0.49        | ~ (v1_ordinal1 @ sk_B)
% 0.21/0.49        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '36'])).
% 0.21/0.49  thf('38', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('39', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('40', plain, ((v1_ordinal1 @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (((r2_xboole_0 @ sk_A @ sk_B)
% 0.21/0.49        | ((sk_B) = (sk_A))
% 0.21/0.49        | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['37', '38', '39', '40'])).
% 0.21/0.49  thf('42', plain, ((((sk_B) = (sk_A)) | (r2_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.21/0.49  thf('43', plain, (((sk_A) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.49  thf('46', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf(d10_xboole_0, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (![X3 : $i, X5 : $i]:
% 0.21/0.49         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.21/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.49  thf('48', plain, ((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) = (sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('49', plain, (((sk_A) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('50', plain, (~ (r1_tarski @ sk_B @ sk_A)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['48', '49'])).
% 0.21/0.49  thf('51', plain,
% 0.21/0.49      (![X24 : $i]:
% 0.21/0.49         ((v2_wellord1 @ (k1_wellord2 @ X24)) | ~ (v3_ordinal1 @ X24))),
% 0.21/0.49      inference('cnf', [status(esa)], [t7_wellord2])).
% 0.21/0.49  thf('52', plain, ((r2_xboole_0 @ sk_A @ sk_B)),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X7)
% 0.21/0.49          | (r2_hidden @ X8 @ X7)
% 0.21/0.49          | ~ (r2_xboole_0 @ X8 @ X7)
% 0.21/0.49          | ~ (v1_ordinal1 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      ((~ (v1_ordinal1 @ sk_A)
% 0.21/0.49        | (r2_hidden @ sk_A @ sk_B)
% 0.21/0.49        | ~ (v3_ordinal1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.49  thf('55', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('56', plain, (![X6 : $i]: ((v1_ordinal1 @ X6) | ~ (v3_ordinal1 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.21/0.49  thf('57', plain, ((v1_ordinal1 @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.49  thf('58', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('59', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['54', '57', '58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (![X22 : $i, X23 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X22)
% 0.21/0.49          | ((X23) = (k1_wellord1 @ (k1_wellord2 @ X22) @ X23))
% 0.21/0.49          | ~ (r2_hidden @ X23 @ X22)
% 0.21/0.49          | ~ (v3_ordinal1 @ X23))),
% 0.21/0.49      inference('cnf', [status(esa)], [t10_wellord2])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      ((~ (v3_ordinal1 @ sk_A)
% 0.21/0.49        | ((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.21/0.49        | ~ (v3_ordinal1 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.49  thf('62', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('63', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('64', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (v3_ordinal1 @ X0)
% 0.21/0.49          | ((X1) = (X0))
% 0.21/0.49          | (r2_xboole_0 @ X0 @ X1)
% 0.21/0.49          | ~ (v3_ordinal1 @ X1)
% 0.21/0.49          | ((k2_wellord1 @ (k1_wellord2 @ X0) @ X1) = (k1_wellord2 @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      (![X15 : $i, X16 : $i]:
% 0.21/0.49         (~ (v2_wellord1 @ X15)
% 0.21/0.49          | ~ (r4_wellord1 @ X15 @ 
% 0.21/0.49               (k2_wellord1 @ X15 @ (k1_wellord1 @ X15 @ X16)))
% 0.21/0.49          | ~ (r2_hidden @ X16 @ (k3_relat_1 @ X15))
% 0.21/0.49          | ~ (v1_relat_1 @ X15))),
% 0.21/0.49      inference('cnf', [status(esa)], [t57_wellord1])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.21/0.49             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.21/0.49          | ~ (v3_ordinal1 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.49          | (r2_xboole_0 @ X1 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.49          | ((k1_wellord1 @ (k1_wellord2 @ X1) @ X0) = (X1))
% 0.21/0.49          | ~ (v3_ordinal1 @ X1)
% 0.21/0.49          | ~ (v1_relat_1 @ (k1_wellord2 @ X1))
% 0.21/0.49          | ~ (r2_hidden @ X0 @ (k3_relat_1 @ (k1_wellord2 @ X1)))
% 0.21/0.49          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.49  thf('68', plain, (![X21 : $i]: (v1_relat_1 @ (k1_wellord2 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('69', plain, (![X17 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X17)) = (X17))),
% 0.21/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (r4_wellord1 @ (k1_wellord2 @ X1) @ 
% 0.21/0.49             (k1_wellord2 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0)))
% 0.21/0.49          | ~ (v3_ordinal1 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.49          | (r2_xboole_0 @ X1 @ (k1_wellord1 @ (k1_wellord2 @ X1) @ X0))
% 0.21/0.49          | ((k1_wellord1 @ (k1_wellord2 @ X1) @ X0) = (X1))
% 0.21/0.49          | ~ (v3_ordinal1 @ X1)
% 0.21/0.49          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.49          | ~ (v2_wellord1 @ (k1_wellord2 @ X1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      ((~ (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.21/0.49        | ~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.21/0.49        | ~ (r2_hidden @ sk_A @ sk_B)
% 0.21/0.49        | ~ (v3_ordinal1 @ sk_B)
% 0.21/0.49        | ((k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A) = (sk_B))
% 0.21/0.49        | (r2_xboole_0 @ sk_B @ (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))
% 0.21/0.49        | ~ (v3_ordinal1 @ (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['64', '70'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      ((r4_wellord1 @ (k1_wellord2 @ sk_A) @ (k1_wellord2 @ sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t50_wellord1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( v1_relat_1 @ B ) =>
% 0.21/0.49           ( ( r4_wellord1 @ A @ B ) => ( r4_wellord1 @ B @ A ) ) ) ) ))).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X13)
% 0.21/0.49          | (r4_wellord1 @ X13 @ X14)
% 0.21/0.49          | ~ (r4_wellord1 @ X14 @ X13)
% 0.21/0.49          | ~ (v1_relat_1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t50_wellord1])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      ((~ (v1_relat_1 @ (k1_wellord2 @ sk_A))
% 0.21/0.49        | (r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))
% 0.21/0.49        | ~ (v1_relat_1 @ (k1_wellord2 @ sk_B)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.49  thf('75', plain, (![X21 : $i]: (v1_relat_1 @ (k1_wellord2 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('76', plain, (![X21 : $i]: (v1_relat_1 @ (k1_wellord2 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      ((r4_wellord1 @ (k1_wellord2 @ sk_B) @ (k1_wellord2 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.21/0.49  thf('78', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.49      inference('demod', [status(thm)], ['54', '57', '58'])).
% 0.21/0.49  thf('79', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('80', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.49  thf('81', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.49  thf('82', plain, (((sk_A) = (k1_wellord1 @ (k1_wellord2 @ sk_B) @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.21/0.49  thf('83', plain, ((v3_ordinal1 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('84', plain,
% 0.21/0.49      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B))
% 0.21/0.49        | ((sk_A) = (sk_B))
% 0.21/0.49        | (r2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)],
% 0.21/0.49                ['71', '77', '78', '79', '80', '81', '82', '83'])).
% 0.21/0.49  thf('85', plain, (((sk_A) != (sk_B))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('86', plain,
% 0.21/0.49      ((~ (v2_wellord1 @ (k1_wellord2 @ sk_B)) | (r2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.49      inference('simplify_reflect-', [status(thm)], ['84', '85'])).
% 0.21/0.49  thf('87', plain, ((~ (v3_ordinal1 @ sk_B) | (r2_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['51', '86'])).
% 0.21/0.49  thf('88', plain, ((v3_ordinal1 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('89', plain, ((r2_xboole_0 @ sk_B @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['87', '88'])).
% 0.21/0.49  thf('90', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (r2_xboole_0 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.21/0.49  thf('91', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.49  thf('92', plain, ($false), inference('demod', [status(thm)], ['50', '91'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
