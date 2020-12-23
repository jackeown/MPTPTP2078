%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TgBU040nin

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:35 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 451 expanded)
%              Number of leaves         :   25 ( 155 expanded)
%              Depth                    :   17
%              Number of atoms          :  849 (3967 expanded)
%              Number of equality atoms :   45 ( 257 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t73_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ! [C: $i] :
            ( ( r2_hidden @ C @ A )
           => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) )
       => ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C @ X14 @ X15 ) @ X15 )
      | ( r1_tarski @ ( k6_relat_1 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('5',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

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

thf('8',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
       != ( k1_wellord2 @ X16 ) )
      | ( ( k3_relat_1 @ X17 )
        = X16 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('9',plain,(
    ! [X16: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X16 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
        = X16 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('10',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X7: $i] :
      ( ( ( k3_relat_1 @ X7 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k3_relat_1 @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X0 ) )
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('19',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','20'])).

thf('22',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17
       != ( k1_wellord2 @ X16 ) )
      | ~ ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X17 )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('27',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X16 ) )
      | ~ ( r1_tarski @ X18 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ ( k1_wellord2 @ X16 ) )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ~ ( r2_hidden @ X18 @ X16 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('29',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X18 @ X19 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ ( k1_wellord2 @ X16 ) )
      | ~ ( r2_hidden @ X19 @ X16 )
      | ~ ( r2_hidden @ X18 @ X16 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) @ ( sk_C @ ( k1_wellord2 @ X0 ) @ X0 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X14 @ X15 ) @ ( sk_C @ X14 @ X15 ) ) @ X14 )
      | ( r1_tarski @ ( k6_relat_1 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ X11 ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('40',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('41',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('44',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('45',plain,(
    ! [X9: $i] :
      ( ( r1_tarski @ X9 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X9 ) @ ( k2_relat_1 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('48',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_C @ X14 @ X15 ) @ X15 )
      | ( r1_tarski @ ( k6_relat_1 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X0 ) @ ( k1_wellord2 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_C @ X1 @ X0 ) ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X14 @ X15 ) @ ( sk_C @ X14 @ X15 ) ) @ X14 )
      | ( r1_tarski @ ( k6_relat_1 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t73_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('55',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k1_wellord2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X8: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('61',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('62',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('63',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('64',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      = ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X16: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X16 ) )
      = X16 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('67',plain,(
    ! [X7: $i] :
      ( ( ( k3_relat_1 @ X7 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X7 ) @ ( k2_relat_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('68',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('69',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( ( k2_xboole_0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X20: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      | ( ( k2_xboole_0 @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
        = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('76',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('77',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('78',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) )
      = X0 ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k1_wellord2 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['65','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['0','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TgBU040nin
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:37:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.58  % Solved by: fo/fo7.sh
% 0.38/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.58  % done 192 iterations in 0.122s
% 0.38/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.58  % SZS output start Refutation
% 0.38/0.58  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.58  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.58  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.38/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.58  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.38/0.58  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.38/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.58  thf(t33_wellord2, conjecture,
% 0.38/0.58    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.38/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.58    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.38/0.58    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.38/0.58  thf('0', plain,
% 0.38/0.58      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.38/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.58  thf(t73_relat_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( ![C:$i]:
% 0.38/0.58           ( ( r2_hidden @ C @ A ) => ( r2_hidden @ ( k4_tarski @ C @ C ) @ B ) ) ) =>
% 0.38/0.58         ( r1_tarski @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.38/0.58  thf('1', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         ((r2_hidden @ (sk_C @ X14 @ X15) @ X15)
% 0.38/0.58          | (r1_tarski @ (k6_relat_1 @ X15) @ X14)
% 0.38/0.58          | ~ (v1_relat_1 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.38/0.58  thf(t25_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ![B:$i]:
% 0.38/0.58         ( ( v1_relat_1 @ B ) =>
% 0.38/0.58           ( ( r1_tarski @ A @ B ) =>
% 0.38/0.58             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.38/0.58               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.38/0.58  thf('2', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X10)
% 0.38/0.58          | (r1_tarski @ (k1_relat_1 @ X11) @ (k1_relat_1 @ X10))
% 0.38/0.58          | ~ (r1_tarski @ X11 @ X10)
% 0.38/0.58          | ~ (v1_relat_1 @ X11))),
% 0.38/0.58      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.38/0.58  thf('3', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X0)
% 0.38/0.58          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X1))
% 0.38/0.58          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X1)) @ (k1_relat_1 @ X0))
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.38/0.58  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.38/0.58  thf('4', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.58  thf(t71_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.38/0.58       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.38/0.58  thf('5', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf('6', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X0)
% 0.38/0.58          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.58          | (r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.38/0.58  thf('7', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r1_tarski @ X1 @ (k1_relat_1 @ X0))
% 0.38/0.58          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.58  thf(d1_wellord2, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ B ) =>
% 0.38/0.58       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.38/0.58         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.38/0.58           ( ![C:$i,D:$i]:
% 0.38/0.58             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.38/0.58               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.38/0.58                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.38/0.58  thf('8', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i]:
% 0.38/0.58         (((X17) != (k1_wellord2 @ X16))
% 0.38/0.58          | ((k3_relat_1 @ X17) = (X16))
% 0.38/0.58          | ~ (v1_relat_1 @ X17))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.38/0.58  thf('9', plain,
% 0.38/0.58      (![X16 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ (k1_wellord2 @ X16))
% 0.38/0.58          | ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16)))),
% 0.38/0.58      inference('simplify', [status(thm)], ['8'])).
% 0.38/0.58  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.38/0.58  thf('10', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.58  thf('11', plain, (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.38/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf(d6_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( ( k3_relat_1 @ A ) =
% 0.38/0.58         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.38/0.58  thf('12', plain,
% 0.38/0.58      (![X7 : $i]:
% 0.38/0.58         (((k3_relat_1 @ X7)
% 0.38/0.58            = (k2_xboole_0 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 0.38/0.58          | ~ (v1_relat_1 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.38/0.58  thf(t7_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.38/0.58  thf('13', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.38/0.58      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.58  thf('14', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.38/0.58          | ~ (v1_relat_1 @ X0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['12', '13'])).
% 0.38/0.58  thf(d10_xboole_0, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.38/0.58  thf('15', plain,
% 0.38/0.58      (![X0 : $i, X2 : $i]:
% 0.38/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.58  thf('16', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X0)
% 0.38/0.58          | ~ (r1_tarski @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.38/0.58          | ((k3_relat_1 @ X0) = (k1_relat_1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.58  thf('17', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | ((k3_relat_1 @ (k1_wellord2 @ X0))
% 0.38/0.58              = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['11', '16'])).
% 0.38/0.58  thf('18', plain, (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.38/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf('19', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.58  thf('20', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.38/0.58  thf('21', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.38/0.58          | (r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.38/0.58          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.58      inference('sup-', [status(thm)], ['7', '20'])).
% 0.38/0.58  thf('22', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.58  thf('23', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r2_hidden @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ X0)
% 0.38/0.58          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.58  thf('24', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.38/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.58  thf('25', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.58  thf('26', plain,
% 0.38/0.58      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.38/0.58         (((X17) != (k1_wellord2 @ X16))
% 0.38/0.58          | ~ (r2_hidden @ X18 @ X16)
% 0.38/0.58          | ~ (r2_hidden @ X19 @ X16)
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ X18 @ X19) @ X17)
% 0.38/0.58          | ~ (r1_tarski @ X18 @ X19)
% 0.38/0.58          | ~ (v1_relat_1 @ X17))),
% 0.38/0.58      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.38/0.58  thf('27', plain,
% 0.38/0.58      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ (k1_wellord2 @ X16))
% 0.38/0.58          | ~ (r1_tarski @ X18 @ X19)
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ X18 @ X19) @ (k1_wellord2 @ X16))
% 0.38/0.58          | ~ (r2_hidden @ X19 @ X16)
% 0.38/0.58          | ~ (r2_hidden @ X18 @ X16))),
% 0.38/0.58      inference('simplify', [status(thm)], ['26'])).
% 0.38/0.58  thf('28', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.58  thf('29', plain,
% 0.38/0.58      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X18 @ X19)
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ X18 @ X19) @ (k1_wellord2 @ X16))
% 0.38/0.58          | ~ (r2_hidden @ X19 @ X16)
% 0.38/0.58          | ~ (r2_hidden @ X18 @ X16))),
% 0.38/0.58      inference('demod', [status(thm)], ['27', '28'])).
% 0.38/0.58  thf('30', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r2_hidden @ X0 @ X1)
% 0.38/0.58          | ~ (r2_hidden @ X0 @ X1)
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['25', '29'])).
% 0.38/0.58  thf('31', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.58      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.58  thf('32', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | (r2_hidden @ 
% 0.38/0.58             (k4_tarski @ (sk_C @ (k1_wellord2 @ X0) @ X0) @ 
% 0.38/0.58              (sk_C @ (k1_wellord2 @ X0) @ X0)) @ 
% 0.38/0.58             (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['23', '31'])).
% 0.38/0.58  thf('33', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         (~ (r2_hidden @ 
% 0.38/0.58             (k4_tarski @ (sk_C @ X14 @ X15) @ (sk_C @ X14 @ X15)) @ X14)
% 0.38/0.58          | (r1_tarski @ (k6_relat_1 @ X15) @ X14)
% 0.38/0.58          | ~ (v1_relat_1 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.38/0.58  thf('34', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.38/0.58          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.38/0.58  thf('35', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.58  thf('36', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['34', '35'])).
% 0.38/0.58  thf('37', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X10)
% 0.38/0.58          | (r1_tarski @ (k1_relat_1 @ X11) @ (k1_relat_1 @ X10))
% 0.38/0.58          | ~ (r1_tarski @ X11 @ X10)
% 0.38/0.58          | ~ (v1_relat_1 @ X11))),
% 0.38/0.58      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.38/0.58  thf('38', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.58          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.38/0.58             (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['36', '37'])).
% 0.38/0.58  thf('39', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.58  thf('40', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf('41', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.58  thf('42', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.38/0.58  thf('43', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.38/0.58  thf('44', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('clc', [status(thm)], ['42', '43'])).
% 0.38/0.58  thf(t21_relat_1, axiom,
% 0.38/0.58    (![A:$i]:
% 0.38/0.58     ( ( v1_relat_1 @ A ) =>
% 0.38/0.58       ( r1_tarski @
% 0.38/0.58         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.38/0.58  thf('45', plain,
% 0.38/0.58      (![X9 : $i]:
% 0.38/0.58         ((r1_tarski @ X9 @ 
% 0.38/0.58           (k2_zfmisc_1 @ (k1_relat_1 @ X9) @ (k2_relat_1 @ X9)))
% 0.38/0.58          | ~ (v1_relat_1 @ X9))),
% 0.38/0.58      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.38/0.58  thf('46', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.38/0.58           (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))
% 0.38/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('sup+', [status(thm)], ['44', '45'])).
% 0.38/0.58  thf('47', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.58  thf('48', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (r1_tarski @ (k1_wellord2 @ X0) @ 
% 0.38/0.58          (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['46', '47'])).
% 0.38/0.58  thf('49', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         ((r2_hidden @ (sk_C @ X14 @ X15) @ X15)
% 0.38/0.58          | (r1_tarski @ (k6_relat_1 @ X15) @ X14)
% 0.38/0.58          | ~ (v1_relat_1 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.38/0.58  thf('50', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         ((r2_hidden @ (k4_tarski @ X0 @ X0) @ (k1_wellord2 @ X1))
% 0.38/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.38/0.58      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.58  thf('51', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X1)
% 0.38/0.58          | (r1_tarski @ (k6_relat_1 @ X0) @ X1)
% 0.38/0.58          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_C @ X1 @ X0)) @ 
% 0.38/0.58             (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['49', '50'])).
% 0.38/0.58  thf('52', plain,
% 0.38/0.58      (![X14 : $i, X15 : $i]:
% 0.38/0.58         (~ (r2_hidden @ 
% 0.38/0.58             (k4_tarski @ (sk_C @ X14 @ X15) @ (sk_C @ X14 @ X15)) @ X14)
% 0.38/0.58          | (r1_tarski @ (k6_relat_1 @ X15) @ X14)
% 0.38/0.58          | ~ (v1_relat_1 @ X14))),
% 0.38/0.58      inference('cnf', [status(esa)], [t73_relat_1])).
% 0.38/0.58  thf('53', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))
% 0.38/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.38/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.38/0.58          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.38/0.58  thf('54', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.58  thf('55', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.58  thf('56', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))
% 0.38/0.58          | (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.38/0.58  thf('57', plain,
% 0.38/0.58      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k1_wellord2 @ X0))),
% 0.38/0.58      inference('simplify', [status(thm)], ['56'])).
% 0.38/0.58  thf('58', plain,
% 0.38/0.58      (![X10 : $i, X11 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ X10)
% 0.38/0.58          | (r1_tarski @ (k2_relat_1 @ X11) @ (k2_relat_1 @ X10))
% 0.38/0.58          | ~ (r1_tarski @ X11 @ X10)
% 0.38/0.58          | ~ (v1_relat_1 @ X11))),
% 0.38/0.58      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.38/0.58  thf('59', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.38/0.58          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.38/0.58             (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.38/0.58  thf('60', plain, (![X8 : $i]: (v1_relat_1 @ (k6_relat_1 @ X8))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.38/0.58  thf('61', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.38/0.58      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.38/0.58  thf('62', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.58  thf('63', plain,
% 0.38/0.58      (![X0 : $i]: (r1_tarski @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.38/0.58  thf(t12_xboole_1, axiom,
% 0.38/0.58    (![A:$i,B:$i]:
% 0.38/0.58     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.58  thf('64', plain,
% 0.38/0.58      (![X3 : $i, X4 : $i]:
% 0.38/0.58         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.38/0.58      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.58  thf('65', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58           = (k2_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['63', '64'])).
% 0.38/0.58  thf('66', plain, (![X16 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X16)) = (X16))),
% 0.38/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.38/0.58  thf('67', plain,
% 0.38/0.58      (![X7 : $i]:
% 0.38/0.58         (((k3_relat_1 @ X7)
% 0.38/0.58            = (k2_xboole_0 @ (k1_relat_1 @ X7) @ (k2_relat_1 @ X7)))
% 0.38/0.58          | ~ (v1_relat_1 @ X7))),
% 0.38/0.58      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.38/0.58  thf('68', plain,
% 0.38/0.58      (![X5 : $i, X6 : $i]: (r1_tarski @ X5 @ (k2_xboole_0 @ X5 @ X6))),
% 0.38/0.58      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.38/0.58  thf('69', plain,
% 0.38/0.58      (![X0 : $i, X2 : $i]:
% 0.38/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.38/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.38/0.58  thf('70', plain,
% 0.38/0.58      (![X0 : $i, X1 : $i]:
% 0.38/0.58         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.38/0.58          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['68', '69'])).
% 0.38/0.58  thf('71', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r1_tarski @ (k3_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.38/0.58          | ~ (v1_relat_1 @ X0)
% 0.38/0.58          | ((k2_xboole_0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.38/0.58              = (k1_relat_1 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['67', '70'])).
% 0.38/0.58  thf('72', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | ((k2_xboole_0 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ 
% 0.38/0.58              (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58              = (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('sup-', [status(thm)], ['66', '71'])).
% 0.38/0.58  thf('73', plain, (![X20 : $i]: (v1_relat_1 @ (k1_wellord2 @ X20))),
% 0.38/0.58      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.38/0.58  thf('74', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58          | ((k2_xboole_0 @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ 
% 0.38/0.58              (k2_relat_1 @ (k1_wellord2 @ X0)))
% 0.38/0.58              = (k1_relat_1 @ (k1_wellord2 @ X0))))),
% 0.38/0.58      inference('demod', [status(thm)], ['72', '73'])).
% 0.38/0.58  thf('75', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('clc', [status(thm)], ['42', '43'])).
% 0.38/0.58  thf('76', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.38/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.38/0.58  thf('77', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('clc', [status(thm)], ['42', '43'])).
% 0.38/0.58  thf('78', plain, (![X0 : $i]: ((X0) = (k1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.38/0.58      inference('clc', [status(thm)], ['42', '43'])).
% 0.38/0.58  thf('79', plain,
% 0.38/0.58      (![X0 : $i]:
% 0.38/0.58         ((k2_xboole_0 @ X0 @ (k2_relat_1 @ (k1_wellord2 @ X0))) = (X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 0.38/0.58  thf('80', plain, (![X0 : $i]: ((k2_relat_1 @ (k1_wellord2 @ X0)) = (X0))),
% 0.38/0.58      inference('sup+', [status(thm)], ['65', '79'])).
% 0.38/0.58  thf('81', plain,
% 0.38/0.58      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.38/0.58      inference('demod', [status(thm)], ['48', '80'])).
% 0.38/0.58  thf('82', plain, ($false), inference('demod', [status(thm)], ['0', '81'])).
% 0.38/0.58  
% 0.38/0.58  % SZS output end Refutation
% 0.38/0.58  
% 0.41/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
