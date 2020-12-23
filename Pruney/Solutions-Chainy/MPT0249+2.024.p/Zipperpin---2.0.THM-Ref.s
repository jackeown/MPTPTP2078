%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1VmEcenJ4g

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:41 EST 2020

% Result     : Theorem 13.88s
% Output     : Refutation 13.88s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 391 expanded)
%              Number of leaves         :   30 ( 126 expanded)
%              Depth                    :   26
%              Number of atoms          :  910 (3169 expanded)
%              Number of equality atoms :   98 ( 423 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ( X13 != X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r1_tarski @ X18 @ ( k2_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('5',plain,(
    ! [X66: $i,X67: $i] :
      ( ( X67
        = ( k1_tarski @ X66 ) )
      | ( X67 = k1_xboole_0 )
      | ~ ( r1_tarski @ X67 @ ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_C_2
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( sk_C_2
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('16',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('17',plain,(
    ! [X67: $i,X68: $i] :
      ( ( r1_tarski @ X67 @ ( k1_tarski @ X68 ) )
      | ( X67 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('18',plain,(
    ! [X68: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X68 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('29',plain,(
    ! [X25: $i,X26: $i] :
      ( ( k4_xboole_0 @ X25 @ ( k2_xboole_0 @ X25 @ X26 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','30'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_xboole_0 @ X27 @ X29 )
      | ( ( k4_xboole_0 @ X27 @ X29 )
       != X27 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['16','35'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('37',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('38',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('39',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','34'])).

thf('42',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X14: $i] :
      ( r1_tarski @ X14 @ X14 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('44',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ X27 @ X28 )
        = X27 )
      | ~ ( r1_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['36','58'])).

thf('60',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_B_1 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('61',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ X0 ) @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D @ sk_B_1 @ k1_xboole_0 @ X0 ) @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( sk_C_2
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('68',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_2 ),
    inference(demod,[status(thm)],['66','67'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('69',plain,(
    ! [X30: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ( X33 = X30 )
      | ( X32
       != ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('70',plain,(
    ! [X30: $i,X33: $i] :
      ( ( X33 = X30 )
      | ~ ( r2_hidden @ X33 @ ( k1_tarski @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( sk_D @ sk_B_1 @ k1_xboole_0 @ X0 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_A @ sk_B_1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( sk_B_1
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['72','75'])).

thf('77',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('78',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','34'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','57'])).

thf('81',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','79','80'])).

thf('82',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['81','82'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('84',plain,(
    ! [X63: $i,X65: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X63 ) @ X65 )
      | ~ ( r2_hidden @ X63 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('85',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_tarski @ sk_A )
    = sk_C_2 ),
    inference(demod,[status(thm)],['66','67'])).

thf('87',plain,(
    r1_tarski @ sk_C_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k3_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B_1 )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_2 )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( sk_C_2
        = ( k3_xboole_0 @ X0 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_D @ sk_C_2 @ sk_C_2 @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('94',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['14'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( sk_C_2
      = ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_C_2
      = ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['92','98'])).

thf('100',plain,
    ( sk_C_2
    = ( k3_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    sk_C_2 = sk_B_1 ),
    inference('sup+',[status(thm)],['13','100'])).

thf('102',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['101','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1VmEcenJ4g
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:29:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 13.88/14.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.88/14.07  % Solved by: fo/fo7.sh
% 13.88/14.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.88/14.07  % done 14579 iterations in 13.610s
% 13.88/14.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.88/14.07  % SZS output start Refutation
% 13.88/14.07  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 13.88/14.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 13.88/14.07  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 13.88/14.07  thf(sk_A_type, type, sk_A: $i).
% 13.88/14.07  thf(sk_C_2_type, type, sk_C_2: $i).
% 13.88/14.07  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 13.88/14.07  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 13.88/14.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 13.88/14.07  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 13.88/14.07  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 13.88/14.07  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 13.88/14.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 13.88/14.07  thf(sk_B_type, type, sk_B: $i > $i).
% 13.88/14.07  thf(sk_B_1_type, type, sk_B_1: $i).
% 13.88/14.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.88/14.07  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 13.88/14.07  thf(d10_xboole_0, axiom,
% 13.88/14.07    (![A:$i,B:$i]:
% 13.88/14.07     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 13.88/14.07  thf('0', plain,
% 13.88/14.07      (![X13 : $i, X14 : $i]: ((r1_tarski @ X13 @ X14) | ((X13) != (X14)))),
% 13.88/14.07      inference('cnf', [status(esa)], [d10_xboole_0])).
% 13.88/14.07  thf('1', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 13.88/14.07      inference('simplify', [status(thm)], ['0'])).
% 13.88/14.07  thf(t10_xboole_1, axiom,
% 13.88/14.07    (![A:$i,B:$i,C:$i]:
% 13.88/14.07     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 13.88/14.07  thf('2', plain,
% 13.88/14.07      (![X18 : $i, X19 : $i, X20 : $i]:
% 13.88/14.07         (~ (r1_tarski @ X18 @ X19)
% 13.88/14.07          | (r1_tarski @ X18 @ (k2_xboole_0 @ X20 @ X19)))),
% 13.88/14.07      inference('cnf', [status(esa)], [t10_xboole_1])).
% 13.88/14.07  thf('3', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 13.88/14.07      inference('sup-', [status(thm)], ['1', '2'])).
% 13.88/14.07  thf(t44_zfmisc_1, conjecture,
% 13.88/14.07    (![A:$i,B:$i,C:$i]:
% 13.88/14.07     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 13.88/14.07          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 13.88/14.07          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 13.88/14.07  thf(zf_stmt_0, negated_conjecture,
% 13.88/14.07    (~( ![A:$i,B:$i,C:$i]:
% 13.88/14.07        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 13.88/14.07             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 13.88/14.07             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 13.88/14.07    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 13.88/14.07  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 13.88/14.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.88/14.07  thf(l3_zfmisc_1, axiom,
% 13.88/14.07    (![A:$i,B:$i]:
% 13.88/14.07     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 13.88/14.07       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 13.88/14.07  thf('5', plain,
% 13.88/14.07      (![X66 : $i, X67 : $i]:
% 13.88/14.07         (((X67) = (k1_tarski @ X66))
% 13.88/14.07          | ((X67) = (k1_xboole_0))
% 13.88/14.07          | ~ (r1_tarski @ X67 @ (k1_tarski @ X66)))),
% 13.88/14.07      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 13.88/14.07  thf('6', plain,
% 13.88/14.07      (![X0 : $i]:
% 13.88/14.07         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 13.88/14.07          | ((X0) = (k1_xboole_0))
% 13.88/14.07          | ((X0) = (k1_tarski @ sk_A)))),
% 13.88/14.07      inference('sup-', [status(thm)], ['4', '5'])).
% 13.88/14.07  thf('7', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 13.88/14.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.88/14.07  thf('8', plain,
% 13.88/14.07      (![X0 : $i]:
% 13.88/14.07         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 13.88/14.07          | ((X0) = (k1_xboole_0))
% 13.88/14.07          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 13.88/14.07      inference('demod', [status(thm)], ['6', '7'])).
% 13.88/14.07  thf('9', plain,
% 13.88/14.07      ((((sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 13.88/14.07        | ((sk_C_2) = (k1_xboole_0)))),
% 13.88/14.07      inference('sup-', [status(thm)], ['3', '8'])).
% 13.88/14.07  thf('10', plain, (((sk_C_2) != (k1_xboole_0))),
% 13.88/14.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.88/14.07  thf('11', plain, (((sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 13.88/14.07      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 13.88/14.07  thf(t21_xboole_1, axiom,
% 13.88/14.07    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 13.88/14.07  thf('12', plain,
% 13.88/14.07      (![X21 : $i, X22 : $i]:
% 13.88/14.07         ((k3_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22)) = (X21))),
% 13.88/14.07      inference('cnf', [status(esa)], [t21_xboole_1])).
% 13.88/14.07  thf('13', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_B_1))),
% 13.88/14.07      inference('sup+', [status(thm)], ['11', '12'])).
% 13.88/14.07  thf(d4_xboole_0, axiom,
% 13.88/14.07    (![A:$i,B:$i,C:$i]:
% 13.88/14.07     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 13.88/14.07       ( ![D:$i]:
% 13.88/14.07         ( ( r2_hidden @ D @ C ) <=>
% 13.88/14.07           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 13.88/14.07  thf('14', plain,
% 13.88/14.07      (![X4 : $i, X5 : $i, X8 : $i]:
% 13.88/14.07         (((X8) = (k3_xboole_0 @ X4 @ X5))
% 13.88/14.07          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 13.88/14.07          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 13.88/14.07      inference('cnf', [status(esa)], [d4_xboole_0])).
% 13.88/14.07  thf('15', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i]:
% 13.88/14.07         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 13.88/14.07          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 13.88/14.07      inference('eq_fact', [status(thm)], ['14'])).
% 13.88/14.07  thf('16', plain,
% 13.88/14.07      (![X4 : $i, X5 : $i, X8 : $i]:
% 13.88/14.07         (((X8) = (k3_xboole_0 @ X4 @ X5))
% 13.88/14.07          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 13.88/14.07          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 13.88/14.07      inference('cnf', [status(esa)], [d4_xboole_0])).
% 13.88/14.07  thf('17', plain,
% 13.88/14.07      (![X67 : $i, X68 : $i]:
% 13.88/14.07         ((r1_tarski @ X67 @ (k1_tarski @ X68)) | ((X67) != (k1_xboole_0)))),
% 13.88/14.07      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 13.88/14.07  thf('18', plain,
% 13.88/14.07      (![X68 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X68))),
% 13.88/14.07      inference('simplify', [status(thm)], ['17'])).
% 13.88/14.07  thf(t28_xboole_1, axiom,
% 13.88/14.07    (![A:$i,B:$i]:
% 13.88/14.07     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 13.88/14.07  thf('19', plain,
% 13.88/14.07      (![X23 : $i, X24 : $i]:
% 13.88/14.07         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 13.88/14.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 13.88/14.07  thf('20', plain,
% 13.88/14.07      (![X0 : $i]:
% 13.88/14.07         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 13.88/14.07      inference('sup-', [status(thm)], ['18', '19'])).
% 13.88/14.07  thf(t4_xboole_0, axiom,
% 13.88/14.07    (![A:$i,B:$i]:
% 13.88/14.07     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 13.88/14.07            ( r1_xboole_0 @ A @ B ) ) ) & 
% 13.88/14.07       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 13.88/14.07            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 13.88/14.07  thf('21', plain,
% 13.88/14.07      (![X9 : $i, X11 : $i, X12 : $i]:
% 13.88/14.07         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 13.88/14.07          | ~ (r1_xboole_0 @ X9 @ X12))),
% 13.88/14.07      inference('cnf', [status(esa)], [t4_xboole_0])).
% 13.88/14.07  thf('22', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i]:
% 13.88/14.07         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 13.88/14.07          | ~ (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 13.88/14.07      inference('sup-', [status(thm)], ['20', '21'])).
% 13.88/14.07  thf('23', plain,
% 13.88/14.07      (![X0 : $i]:
% 13.88/14.07         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 13.88/14.07      inference('sup-', [status(thm)], ['18', '19'])).
% 13.88/14.07  thf(t100_xboole_1, axiom,
% 13.88/14.07    (![A:$i,B:$i]:
% 13.88/14.07     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 13.88/14.07  thf('24', plain,
% 13.88/14.07      (![X16 : $i, X17 : $i]:
% 13.88/14.07         ((k4_xboole_0 @ X16 @ X17)
% 13.88/14.07           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 13.88/14.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 13.88/14.07  thf('25', plain,
% 13.88/14.07      (![X0 : $i]:
% 13.88/14.07         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))
% 13.88/14.07           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 13.88/14.07      inference('sup+', [status(thm)], ['23', '24'])).
% 13.88/14.07  thf('26', plain,
% 13.88/14.07      (![X21 : $i, X22 : $i]:
% 13.88/14.07         ((k3_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22)) = (X21))),
% 13.88/14.07      inference('cnf', [status(esa)], [t21_xboole_1])).
% 13.88/14.07  thf('27', plain,
% 13.88/14.07      (![X16 : $i, X17 : $i]:
% 13.88/14.07         ((k4_xboole_0 @ X16 @ X17)
% 13.88/14.07           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 13.88/14.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 13.88/14.07  thf('28', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i]:
% 13.88/14.07         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 13.88/14.07           = (k5_xboole_0 @ X0 @ X0))),
% 13.88/14.07      inference('sup+', [status(thm)], ['26', '27'])).
% 13.88/14.07  thf(t46_xboole_1, axiom,
% 13.88/14.07    (![A:$i,B:$i]:
% 13.88/14.07     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 13.88/14.07  thf('29', plain,
% 13.88/14.07      (![X25 : $i, X26 : $i]:
% 13.88/14.07         ((k4_xboole_0 @ X25 @ (k2_xboole_0 @ X25 @ X26)) = (k1_xboole_0))),
% 13.88/14.07      inference('cnf', [status(esa)], [t46_xboole_1])).
% 13.88/14.07  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 13.88/14.07      inference('sup+', [status(thm)], ['28', '29'])).
% 13.88/14.07  thf('31', plain,
% 13.88/14.07      (![X0 : $i]:
% 13.88/14.07         ((k4_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 13.88/14.07      inference('demod', [status(thm)], ['25', '30'])).
% 13.88/14.07  thf(t83_xboole_1, axiom,
% 13.88/14.07    (![A:$i,B:$i]:
% 13.88/14.07     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 13.88/14.07  thf('32', plain,
% 13.88/14.07      (![X27 : $i, X29 : $i]:
% 13.88/14.07         ((r1_xboole_0 @ X27 @ X29) | ((k4_xboole_0 @ X27 @ X29) != (X27)))),
% 13.88/14.07      inference('cnf', [status(esa)], [t83_xboole_1])).
% 13.88/14.07  thf('33', plain,
% 13.88/14.07      (![X0 : $i]:
% 13.88/14.07         (((k1_xboole_0) != (k1_xboole_0))
% 13.88/14.07          | (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))),
% 13.88/14.07      inference('sup-', [status(thm)], ['31', '32'])).
% 13.88/14.07  thf('34', plain,
% 13.88/14.07      (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0))),
% 13.88/14.07      inference('simplify', [status(thm)], ['33'])).
% 13.88/14.07  thf('35', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 13.88/14.07      inference('demod', [status(thm)], ['22', '34'])).
% 13.88/14.07  thf('36', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i]:
% 13.88/14.07         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 13.88/14.07          | ((X1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 13.88/14.07      inference('sup-', [status(thm)], ['16', '35'])).
% 13.88/14.07  thf(d1_xboole_0, axiom,
% 13.88/14.07    (![A:$i]:
% 13.88/14.07     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 13.88/14.07  thf('37', plain,
% 13.88/14.07      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 13.88/14.07      inference('cnf', [status(esa)], [d1_xboole_0])).
% 13.88/14.07  thf('38', plain,
% 13.88/14.07      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 13.88/14.07         (~ (r2_hidden @ X7 @ X6)
% 13.88/14.07          | (r2_hidden @ X7 @ X5)
% 13.88/14.07          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 13.88/14.07      inference('cnf', [status(esa)], [d4_xboole_0])).
% 13.88/14.07  thf('39', plain,
% 13.88/14.07      (![X4 : $i, X5 : $i, X7 : $i]:
% 13.88/14.07         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 13.88/14.07      inference('simplify', [status(thm)], ['38'])).
% 13.88/14.07  thf('40', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i]:
% 13.88/14.07         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 13.88/14.07          | (r2_hidden @ (sk_B @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 13.88/14.07      inference('sup-', [status(thm)], ['37', '39'])).
% 13.88/14.07  thf('41', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 13.88/14.07      inference('demod', [status(thm)], ['22', '34'])).
% 13.88/14.07  thf('42', plain,
% 13.88/14.07      (![X0 : $i]: (v1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 13.88/14.07      inference('sup-', [status(thm)], ['40', '41'])).
% 13.88/14.07  thf('43', plain, (![X14 : $i]: (r1_tarski @ X14 @ X14)),
% 13.88/14.07      inference('simplify', [status(thm)], ['0'])).
% 13.88/14.07  thf('44', plain,
% 13.88/14.07      (![X23 : $i, X24 : $i]:
% 13.88/14.07         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 13.88/14.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 13.88/14.07  thf('45', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 13.88/14.07      inference('sup-', [status(thm)], ['43', '44'])).
% 13.88/14.07  thf('46', plain,
% 13.88/14.07      (![X9 : $i, X10 : $i]:
% 13.88/14.07         ((r1_xboole_0 @ X9 @ X10)
% 13.88/14.07          | (r2_hidden @ (sk_C @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 13.88/14.07      inference('cnf', [status(esa)], [t4_xboole_0])).
% 13.88/14.07  thf('47', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 13.88/14.07      inference('cnf', [status(esa)], [d1_xboole_0])).
% 13.88/14.07  thf('48', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i]:
% 13.88/14.07         ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 13.88/14.07      inference('sup-', [status(thm)], ['46', '47'])).
% 13.88/14.07  thf('49', plain,
% 13.88/14.07      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 13.88/14.07      inference('sup-', [status(thm)], ['45', '48'])).
% 13.88/14.07  thf('50', plain,
% 13.88/14.07      (![X27 : $i, X28 : $i]:
% 13.88/14.07         (((k4_xboole_0 @ X27 @ X28) = (X27)) | ~ (r1_xboole_0 @ X27 @ X28))),
% 13.88/14.07      inference('cnf', [status(esa)], [t83_xboole_1])).
% 13.88/14.07  thf('51', plain,
% 13.88/14.07      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k4_xboole_0 @ X0 @ X0) = (X0)))),
% 13.88/14.07      inference('sup-', [status(thm)], ['49', '50'])).
% 13.88/14.07  thf('52', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 13.88/14.07      inference('sup-', [status(thm)], ['43', '44'])).
% 13.88/14.07  thf('53', plain,
% 13.88/14.07      (![X16 : $i, X17 : $i]:
% 13.88/14.07         ((k4_xboole_0 @ X16 @ X17)
% 13.88/14.07           = (k5_xboole_0 @ X16 @ (k3_xboole_0 @ X16 @ X17)))),
% 13.88/14.07      inference('cnf', [status(esa)], [t100_xboole_1])).
% 13.88/14.07  thf('54', plain,
% 13.88/14.07      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 13.88/14.07      inference('sup+', [status(thm)], ['52', '53'])).
% 13.88/14.07  thf('55', plain,
% 13.88/14.07      (![X0 : $i]: (((X0) = (k5_xboole_0 @ X0 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 13.88/14.07      inference('sup+', [status(thm)], ['51', '54'])).
% 13.88/14.07  thf('56', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 13.88/14.07      inference('sup+', [status(thm)], ['28', '29'])).
% 13.88/14.07  thf('57', plain,
% 13.88/14.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 13.88/14.07      inference('sup+', [status(thm)], ['55', '56'])).
% 13.88/14.07  thf('58', plain,
% 13.88/14.07      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 13.88/14.07      inference('sup-', [status(thm)], ['42', '57'])).
% 13.88/14.07  thf('59', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i]:
% 13.88/14.07         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 13.88/14.07          | ((X1) = (k1_xboole_0)))),
% 13.88/14.07      inference('demod', [status(thm)], ['36', '58'])).
% 13.88/14.07  thf('60', plain, (((k3_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_B_1))),
% 13.88/14.07      inference('sup+', [status(thm)], ['11', '12'])).
% 13.88/14.07  thf('61', plain,
% 13.88/14.07      (![X4 : $i, X5 : $i, X7 : $i]:
% 13.88/14.07         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 13.88/14.07      inference('simplify', [status(thm)], ['38'])).
% 13.88/14.07  thf('62', plain,
% 13.88/14.07      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | (r2_hidden @ X0 @ sk_C_2))),
% 13.88/14.07      inference('sup-', [status(thm)], ['60', '61'])).
% 13.88/14.07  thf('63', plain,
% 13.88/14.07      (![X0 : $i]:
% 13.88/14.07         (((sk_B_1) = (k1_xboole_0))
% 13.88/14.07          | (r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ X0) @ sk_C_2))),
% 13.88/14.07      inference('sup-', [status(thm)], ['59', '62'])).
% 13.88/14.07  thf('64', plain, (((sk_B_1) != (k1_xboole_0))),
% 13.88/14.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.88/14.07  thf('65', plain,
% 13.88/14.07      (![X0 : $i]: (r2_hidden @ (sk_D @ sk_B_1 @ k1_xboole_0 @ X0) @ sk_C_2)),
% 13.88/14.07      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 13.88/14.07  thf('66', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 13.88/14.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.88/14.07  thf('67', plain, (((sk_C_2) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 13.88/14.07      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 13.88/14.07  thf('68', plain, (((k1_tarski @ sk_A) = (sk_C_2))),
% 13.88/14.07      inference('demod', [status(thm)], ['66', '67'])).
% 13.88/14.07  thf(d1_tarski, axiom,
% 13.88/14.07    (![A:$i,B:$i]:
% 13.88/14.07     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 13.88/14.07       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 13.88/14.07  thf('69', plain,
% 13.88/14.07      (![X30 : $i, X32 : $i, X33 : $i]:
% 13.88/14.07         (~ (r2_hidden @ X33 @ X32)
% 13.88/14.07          | ((X33) = (X30))
% 13.88/14.07          | ((X32) != (k1_tarski @ X30)))),
% 13.88/14.07      inference('cnf', [status(esa)], [d1_tarski])).
% 13.88/14.07  thf('70', plain,
% 13.88/14.07      (![X30 : $i, X33 : $i]:
% 13.88/14.07         (((X33) = (X30)) | ~ (r2_hidden @ X33 @ (k1_tarski @ X30)))),
% 13.88/14.07      inference('simplify', [status(thm)], ['69'])).
% 13.88/14.07  thf('71', plain,
% 13.88/14.07      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_2) | ((X0) = (sk_A)))),
% 13.88/14.07      inference('sup-', [status(thm)], ['68', '70'])).
% 13.88/14.07  thf('72', plain, (![X0 : $i]: ((sk_D @ sk_B_1 @ k1_xboole_0 @ X0) = (sk_A))),
% 13.88/14.07      inference('sup-', [status(thm)], ['65', '71'])).
% 13.88/14.07  thf('73', plain,
% 13.88/14.07      (![X4 : $i, X5 : $i, X8 : $i]:
% 13.88/14.07         (((X8) = (k3_xboole_0 @ X4 @ X5))
% 13.88/14.07          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 13.88/14.07          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 13.88/14.07      inference('cnf', [status(esa)], [d4_xboole_0])).
% 13.88/14.07  thf('74', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 13.88/14.07      inference('cnf', [status(esa)], [d1_xboole_0])).
% 13.88/14.07  thf('75', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.88/14.07         ((r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 13.88/14.07          | ((X2) = (k3_xboole_0 @ X1 @ X0))
% 13.88/14.07          | ~ (v1_xboole_0 @ X0))),
% 13.88/14.07      inference('sup-', [status(thm)], ['73', '74'])).
% 13.88/14.07  thf('76', plain,
% 13.88/14.07      (![X0 : $i]:
% 13.88/14.07         ((r2_hidden @ sk_A @ sk_B_1)
% 13.88/14.07          | ~ (v1_xboole_0 @ k1_xboole_0)
% 13.88/14.07          | ((sk_B_1) = (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 13.88/14.07      inference('sup+', [status(thm)], ['72', '75'])).
% 13.88/14.07  thf('77', plain,
% 13.88/14.07      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 13.88/14.07      inference('cnf', [status(esa)], [d1_xboole_0])).
% 13.88/14.07  thf('78', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 13.88/14.07      inference('demod', [status(thm)], ['22', '34'])).
% 13.88/14.07  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.88/14.07      inference('sup-', [status(thm)], ['77', '78'])).
% 13.88/14.07  thf('80', plain,
% 13.88/14.07      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 13.88/14.07      inference('sup-', [status(thm)], ['42', '57'])).
% 13.88/14.07  thf('81', plain,
% 13.88/14.07      (((r2_hidden @ sk_A @ sk_B_1) | ((sk_B_1) = (k1_xboole_0)))),
% 13.88/14.07      inference('demod', [status(thm)], ['76', '79', '80'])).
% 13.88/14.07  thf('82', plain, (((sk_B_1) != (k1_xboole_0))),
% 13.88/14.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.88/14.07  thf('83', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 13.88/14.07      inference('simplify_reflect-', [status(thm)], ['81', '82'])).
% 13.88/14.07  thf(l1_zfmisc_1, axiom,
% 13.88/14.07    (![A:$i,B:$i]:
% 13.88/14.07     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 13.88/14.07  thf('84', plain,
% 13.88/14.07      (![X63 : $i, X65 : $i]:
% 13.88/14.07         ((r1_tarski @ (k1_tarski @ X63) @ X65) | ~ (r2_hidden @ X63 @ X65))),
% 13.88/14.07      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 13.88/14.07  thf('85', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 13.88/14.07      inference('sup-', [status(thm)], ['83', '84'])).
% 13.88/14.07  thf('86', plain, (((k1_tarski @ sk_A) = (sk_C_2))),
% 13.88/14.07      inference('demod', [status(thm)], ['66', '67'])).
% 13.88/14.07  thf('87', plain, ((r1_tarski @ sk_C_2 @ sk_B_1)),
% 13.88/14.07      inference('demod', [status(thm)], ['85', '86'])).
% 13.88/14.07  thf('88', plain,
% 13.88/14.07      (![X23 : $i, X24 : $i]:
% 13.88/14.07         (((k3_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_tarski @ X23 @ X24))),
% 13.88/14.07      inference('cnf', [status(esa)], [t28_xboole_1])).
% 13.88/14.07  thf('89', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B_1) = (sk_C_2))),
% 13.88/14.07      inference('sup-', [status(thm)], ['87', '88'])).
% 13.88/14.07  thf('90', plain,
% 13.88/14.07      (![X4 : $i, X5 : $i, X7 : $i]:
% 13.88/14.07         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 13.88/14.07      inference('simplify', [status(thm)], ['38'])).
% 13.88/14.07  thf('91', plain,
% 13.88/14.07      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_C_2) | (r2_hidden @ X0 @ sk_B_1))),
% 13.88/14.07      inference('sup-', [status(thm)], ['89', '90'])).
% 13.88/14.07  thf('92', plain,
% 13.88/14.07      (![X0 : $i]:
% 13.88/14.07         (((sk_C_2) = (k3_xboole_0 @ X0 @ sk_C_2))
% 13.88/14.07          | (r2_hidden @ (sk_D @ sk_C_2 @ sk_C_2 @ X0) @ sk_B_1))),
% 13.88/14.07      inference('sup-', [status(thm)], ['15', '91'])).
% 13.88/14.07  thf('93', plain,
% 13.88/14.07      (![X0 : $i, X1 : $i]:
% 13.88/14.07         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 13.88/14.07          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 13.88/14.07      inference('eq_fact', [status(thm)], ['14'])).
% 13.88/14.08  thf('94', plain,
% 13.88/14.08      (![X4 : $i, X5 : $i, X8 : $i]:
% 13.88/14.08         (((X8) = (k3_xboole_0 @ X4 @ X5))
% 13.88/14.08          | ~ (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 13.88/14.08          | ~ (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X4)
% 13.88/14.08          | ~ (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 13.88/14.08      inference('cnf', [status(esa)], [d4_xboole_0])).
% 13.88/14.08  thf('95', plain,
% 13.88/14.08      (![X0 : $i, X1 : $i]:
% 13.88/14.08         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 13.88/14.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 13.88/14.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 13.88/14.08          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 13.88/14.08      inference('sup-', [status(thm)], ['93', '94'])).
% 13.88/14.08  thf('96', plain,
% 13.88/14.08      (![X0 : $i, X1 : $i]:
% 13.88/14.08         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 13.88/14.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 13.88/14.08          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 13.88/14.08      inference('simplify', [status(thm)], ['95'])).
% 13.88/14.08  thf('97', plain,
% 13.88/14.08      (![X0 : $i, X1 : $i]:
% 13.88/14.08         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 13.88/14.08          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 13.88/14.08      inference('eq_fact', [status(thm)], ['14'])).
% 13.88/14.08  thf('98', plain,
% 13.88/14.08      (![X0 : $i, X1 : $i]:
% 13.88/14.08         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 13.88/14.08          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 13.88/14.08      inference('clc', [status(thm)], ['96', '97'])).
% 13.88/14.08  thf('99', plain,
% 13.88/14.08      ((((sk_C_2) = (k3_xboole_0 @ sk_B_1 @ sk_C_2))
% 13.88/14.08        | ((sk_C_2) = (k3_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 13.88/14.08      inference('sup-', [status(thm)], ['92', '98'])).
% 13.88/14.08  thf('100', plain, (((sk_C_2) = (k3_xboole_0 @ sk_B_1 @ sk_C_2))),
% 13.88/14.08      inference('simplify', [status(thm)], ['99'])).
% 13.88/14.08  thf('101', plain, (((sk_C_2) = (sk_B_1))),
% 13.88/14.08      inference('sup+', [status(thm)], ['13', '100'])).
% 13.88/14.08  thf('102', plain, (((sk_B_1) != (sk_C_2))),
% 13.88/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.88/14.08  thf('103', plain, ($false),
% 13.88/14.08      inference('simplify_reflect-', [status(thm)], ['101', '102'])).
% 13.88/14.08  
% 13.88/14.08  % SZS output end Refutation
% 13.88/14.08  
% 13.88/14.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
