%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BCGZ1BuyBx

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:46 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 189 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :   25
%              Number of atoms          :  779 (1709 expanded)
%              Number of equality atoms :  113 ( 193 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t138_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
     => ( ( ( k2_zfmisc_1 @ A @ B )
          = k1_xboole_0 )
        | ( ( r1_tarski @ A @ C )
          & ( r1_tarski @ B @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
       => ( ( ( k2_zfmisc_1 @ A @ B )
            = k1_xboole_0 )
          | ( ( r1_tarski @ A @ C )
            & ( r1_tarski @ B @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t138_zfmisc_1])).

thf('0',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ sk_C @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X16 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('5',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t134_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = ( k2_zfmisc_1 @ C @ D ) )
     => ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 )
        | ( ( A = C )
          & ( B = D ) ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != ( k2_zfmisc_1 @ X26 @ X27 ) )
      | ( X24 = X27 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( X0
        = ( k3_xboole_0 @ sk_B @ sk_D ) )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k3_xboole_0 @ sk_B @ sk_D ) ) ),
    inference(eq_res,[status(thm)],['7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = ( k5_xboole_0 @ sk_B @ sk_B ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_D )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ sk_B @ sk_D )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
    | ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
   <= ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('23',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ X2 @ k1_xboole_0 ) @ ( k2_zfmisc_1 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X16 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('33',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X2 @ X1 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','33'])).

thf('35',plain,
    ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ sk_A @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_D ) )
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('36',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X25 @ X24 )
       != ( k2_zfmisc_1 @ X26 @ X27 ) )
      | ( X25 = X26 ) ) ),
    inference(cnf,[status(esa)],[t134_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
       != ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ( X1
        = ( k3_xboole_0 @ sk_A @ sk_C ) )
      | ( X1 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ sk_C ) ) ),
    inference(eq_res,[status(thm)],['37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C )
      = ( k5_xboole_0 @ sk_A @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('42',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_C )
      = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r1_tarski @ sk_A @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_C )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('47',plain,
    ( ( ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['34','49'])).

thf('51',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('55',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('56',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X20 @ X21 ) @ ( k2_zfmisc_1 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X16 @ X18 ) @ ( k3_xboole_0 @ X17 @ X19 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X16 @ X17 ) @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ ( k2_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ ( k3_xboole_0 @ X2 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','62'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['53','63'])).

thf('65',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_D )
    | ~ ( r1_tarski @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('67',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference('sat_resolution*',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( r1_tarski @ sk_B @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['21','67'])).

thf('69',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['19','68'])).

thf('70',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','33'])).

thf('73',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','62'])).

thf('76',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','74','75'])).

thf('77',plain,(
    $false ),
    inference(simplify,[status(thm)],['76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BCGZ1BuyBx
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:33:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 140 iterations in 0.063s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(t138_zfmisc_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.21/0.52       ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.52         ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52        ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.21/0.52          ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.52            ( ( r1_tarski @ A @ C ) & ( r1_tarski @ B @ D ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t138_zfmisc_1])).
% 0.21/0.52  thf('0', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('1', plain,
% 0.21/0.52      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_B) @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf(t28_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.52  thf('2', plain,
% 0.21/0.52      (![X10 : $i, X11 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.21/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B) @ 
% 0.21/0.52         (k2_zfmisc_1 @ sk_C @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.52  thf(t123_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.21/0.52       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         ((k2_zfmisc_1 @ (k3_xboole_0 @ X16 @ X18) @ (k3_xboole_0 @ X17 @ X19))
% 0.21/0.52           = (k3_xboole_0 @ (k2_zfmisc_1 @ X16 @ X17) @ 
% 0.21/0.52              (k2_zfmisc_1 @ X18 @ X19)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.21/0.52  thf('5', plain,
% 0.21/0.52      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.21/0.52         (k3_xboole_0 @ sk_B @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf(t134_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k2_zfmisc_1 @ C @ D ) ) =>
% 0.21/0.52       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.21/0.52         ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ))).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.52         (((X24) = (k1_xboole_0))
% 0.21/0.52          | ((X25) = (k1_xboole_0))
% 0.21/0.52          | ((k2_zfmisc_1 @ X25 @ X24) != (k2_zfmisc_1 @ X26 @ X27))
% 0.21/0.52          | ((X24) = (X27)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.52          | ((X0) = (k3_xboole_0 @ sk_B @ sk_D))
% 0.21/0.52          | ((X1) = (k1_xboole_0))
% 0.21/0.52          | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      ((((sk_B) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B) = (k3_xboole_0 @ sk_B @ sk_D)))),
% 0.21/0.52      inference('eq_res', [status(thm)], ['7'])).
% 0.21/0.52  thf(t100_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.52  thf('9', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X6 @ X7)
% 0.21/0.52           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      ((((k4_xboole_0 @ sk_B @ sk_D) = (k5_xboole_0 @ sk_B @ sk_B))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf(t21_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.52  thf('12', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X6 @ X7)
% 0.21/0.52           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.52  thf('13', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 0.21/0.52           = (k5_xboole_0 @ X0 @ X0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['11', '12'])).
% 0.21/0.52  thf(t46_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X12 @ (k2_xboole_0 @ X12 @ X13)) = (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.52  thf('15', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      ((((k4_xboole_0 @ sk_B @ sk_D) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.52  thf(l32_xboole_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | (r1_tarski @ sk_B @ sk_D))),
% 0.21/0.52      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (((r1_tarski @ sk_B @ sk_D)
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['18'])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      ((~ (r1_tarski @ sk_A @ sk_C) | ~ (r1_tarski @ sk_B @ sk_D))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      ((~ (r1_tarski @ sk_B @ sk_D)) <= (~ ((r1_tarski @ sk_B @ sk_D)))),
% 0.21/0.52      inference('split', [status(esa)], ['20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.52  thf(d7_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.21/0.52       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((X0) != (k1_xboole_0))
% 0.21/0.52          | (r1_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.52  thf('26', plain,
% 0.21/0.52      (![X1 : $i]:
% 0.21/0.52         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.21/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.52  thf(t127_zfmisc_1, axiom,
% 0.21/0.52    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.52     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.21/0.52       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.52  thf('27', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ (k2_zfmisc_1 @ X22 @ X23))
% 0.21/0.52          | ~ (r1_xboole_0 @ X21 @ X23))),
% 0.21/0.52      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (r1_xboole_0 @ (k2_zfmisc_1 @ X2 @ k1_xboole_0) @ 
% 0.21/0.52          (k2_zfmisc_1 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ (k2_zfmisc_1 @ X2 @ k1_xboole_0) @ 
% 0.21/0.52           (k2_zfmisc_1 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0)))
% 0.21/0.52           = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         ((k2_zfmisc_1 @ (k3_xboole_0 @ X16 @ X18) @ (k3_xboole_0 @ X17 @ X19))
% 0.21/0.52           = (k3_xboole_0 @ (k2_zfmisc_1 @ X16 @ X17) @ 
% 0.21/0.52              (k2_zfmisc_1 @ X18 @ X19)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         ((k2_zfmisc_1 @ (k3_xboole_0 @ X2 @ X1) @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['22', '33'])).
% 0.21/0.52  thf('35', plain,
% 0.21/0.52      (((k2_zfmisc_1 @ (k3_xboole_0 @ sk_A @ sk_C) @ 
% 0.21/0.52         (k3_xboole_0 @ sk_B @ sk_D)) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.52      inference('demod', [status(thm)], ['3', '4'])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.52         (((X24) = (k1_xboole_0))
% 0.21/0.52          | ((X25) = (k1_xboole_0))
% 0.21/0.52          | ((k2_zfmisc_1 @ X25 @ X24) != (k2_zfmisc_1 @ X26 @ X27))
% 0.21/0.52          | ((X25) = (X26)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t134_zfmisc_1])).
% 0.21/0.52  thf('37', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k2_zfmisc_1 @ X1 @ X0) != (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.52          | ((X1) = (k3_xboole_0 @ sk_A @ sk_C))
% 0.21/0.52          | ((X1) = (k1_xboole_0))
% 0.21/0.52          | ((X0) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.52  thf('38', plain,
% 0.21/0.52      ((((sk_B) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k3_xboole_0 @ sk_A @ sk_C)))),
% 0.21/0.52      inference('eq_res', [status(thm)], ['37'])).
% 0.21/0.52  thf('39', plain,
% 0.21/0.52      (![X6 : $i, X7 : $i]:
% 0.21/0.52         ((k4_xboole_0 @ X6 @ X7)
% 0.21/0.52           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.52  thf('40', plain,
% 0.21/0.52      ((((k4_xboole_0 @ sk_A @ sk_C) = (k5_xboole_0 @ sk_A @ sk_A))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.52  thf('41', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.52  thf('42', plain,
% 0.21/0.52      ((((k4_xboole_0 @ sk_A @ sk_C) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.21/0.52  thf('43', plain,
% 0.21/0.52      (![X3 : $i, X4 : $i]:
% 0.21/0.52         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.21/0.52      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.52  thf('44', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | (r1_tarski @ sk_A @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.52  thf('45', plain,
% 0.21/0.52      (((r1_tarski @ sk_A @ sk_C)
% 0.21/0.52        | ((sk_A) = (k1_xboole_0))
% 0.21/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.52  thf('46', plain,
% 0.21/0.52      ((~ (r1_tarski @ sk_A @ sk_C)) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.21/0.52      inference('split', [status(esa)], ['20'])).
% 0.21/0.52  thf('47', plain,
% 0.21/0.52      (((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.52         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.52  thf('48', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('49', plain,
% 0.21/0.52      (((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52         | ((sk_A) = (k1_xboole_0)))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['47', '48'])).
% 0.21/0.52  thf('50', plain,
% 0.21/0.52      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0))))
% 0.21/0.52         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['34', '49'])).
% 0.21/0.52  thf('51', plain,
% 0.21/0.52      ((((sk_A) = (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['50'])).
% 0.21/0.52  thf('52', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('53', plain,
% 0.21/0.52      ((((k2_zfmisc_1 @ k1_xboole_0 @ sk_B) != (k1_xboole_0)))
% 0.21/0.52         <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['51', '52'])).
% 0.21/0.52  thf('54', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.52  thf('55', plain,
% 0.21/0.52      (![X1 : $i]:
% 0.21/0.52         (r1_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))),
% 0.21/0.52      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.52  thf('56', plain,
% 0.21/0.52      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.52         ((r1_xboole_0 @ (k2_zfmisc_1 @ X20 @ X21) @ (k2_zfmisc_1 @ X22 @ X23))
% 0.21/0.52          | ~ (r1_xboole_0 @ X20 @ X22))),
% 0.21/0.52      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.21/0.52  thf('57', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (r1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X2) @ 
% 0.21/0.52          (k2_zfmisc_1 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.52  thf('58', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.21/0.52  thf('59', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ X2) @ 
% 0.21/0.52           (k2_zfmisc_1 @ (k2_xboole_0 @ k1_xboole_0 @ X1) @ X0))
% 0.21/0.52           = (k1_xboole_0))),
% 0.21/0.52      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.52  thf('60', plain,
% 0.21/0.52      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.52         ((k2_zfmisc_1 @ (k3_xboole_0 @ X16 @ X18) @ (k3_xboole_0 @ X17 @ X19))
% 0.21/0.52           = (k3_xboole_0 @ (k2_zfmisc_1 @ X16 @ X17) @ 
% 0.21/0.52              (k2_zfmisc_1 @ X18 @ X19)))),
% 0.21/0.52      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.21/0.52  thf('61', plain,
% 0.21/0.52      (![X8 : $i, X9 : $i]:
% 0.21/0.52         ((k3_xboole_0 @ X8 @ (k2_xboole_0 @ X8 @ X9)) = (X8))),
% 0.21/0.52      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.21/0.52  thf('62', plain,
% 0.21/0.52      (![X0 : $i, X2 : $i]:
% 0.21/0.52         ((k2_zfmisc_1 @ k1_xboole_0 @ (k3_xboole_0 @ X2 @ X0)) = (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.21/0.52  thf('63', plain,
% 0.21/0.52      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['54', '62'])).
% 0.21/0.52  thf('64', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0))) <= (~ ((r1_tarski @ sk_A @ sk_C)))),
% 0.21/0.52      inference('demod', [status(thm)], ['53', '63'])).
% 0.21/0.52  thf('65', plain, (((r1_tarski @ sk_A @ sk_C))),
% 0.21/0.52      inference('simplify', [status(thm)], ['64'])).
% 0.21/0.52  thf('66', plain,
% 0.21/0.52      (~ ((r1_tarski @ sk_B @ sk_D)) | ~ ((r1_tarski @ sk_A @ sk_C))),
% 0.21/0.52      inference('split', [status(esa)], ['20'])).
% 0.21/0.52  thf('67', plain, (~ ((r1_tarski @ sk_B @ sk_D))),
% 0.21/0.52      inference('sat_resolution*', [status(thm)], ['65', '66'])).
% 0.21/0.52  thf('68', plain, (~ (r1_tarski @ sk_B @ sk_D)),
% 0.21/0.52      inference('simpl_trail', [status(thm)], ['21', '67'])).
% 0.21/0.52  thf('69', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('clc', [status(thm)], ['19', '68'])).
% 0.21/0.52  thf('70', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) != (k1_xboole_0))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('71', plain,
% 0.21/0.52      ((((k2_zfmisc_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 0.21/0.52        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['69', '70'])).
% 0.21/0.52  thf('72', plain,
% 0.21/0.52      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['22', '33'])).
% 0.21/0.52  thf('73', plain,
% 0.21/0.52      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.52      inference('demod', [status(thm)], ['71', '72'])).
% 0.21/0.52  thf('74', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['73'])).
% 0.21/0.52  thf('75', plain,
% 0.21/0.52      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.52      inference('sup+', [status(thm)], ['54', '62'])).
% 0.21/0.52  thf('76', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.52      inference('demod', [status(thm)], ['0', '74', '75'])).
% 0.21/0.52  thf('77', plain, ($false), inference('simplify', [status(thm)], ['76'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
