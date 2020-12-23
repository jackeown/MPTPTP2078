%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VTJKAqSJgq

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:09 EST 2020

% Result     : Theorem 6.72s
% Output     : Refutation 6.72s
% Verified   : 
% Statistics : Number of formulae       :  209 (12202 expanded)
%              Number of leaves         :   30 (4150 expanded)
%              Depth                    :   31
%              Number of atoms          : 1712 (88294 expanded)
%              Number of equality atoms :  171 (9513 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t145_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t145_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t144_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( r2_hidden @ X42 @ X43 )
      | ( r2_hidden @ X44 @ X43 )
      | ( X43
        = ( k4_xboole_0 @ X43 @ ( k2_tarski @ X42 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[t144_zfmisc_1])).

thf('2',plain,(
    sk_C
 != ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X20: $i] :
      ( ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ X35 @ ( k4_xboole_0 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t23_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('20',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X21 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['19','22'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X1 @ X3 )
      | ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_xboole_0 @ X30 @ X31 )
      | ( ( k3_xboole_0 @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) )
        = ( k3_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ X2 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['18','27'])).

thf('29',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29'])).

thf(t53_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k2_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('32',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ X35 @ ( k4_xboole_0 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('34',plain,(
    ! [X17: $i] :
      ( r1_tarski @ k1_xboole_0 @ X17 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X1 @ X3 )
      | ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_xboole_0 @ X30 @ X31 )
      | ( ( k3_xboole_0 @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) )
        = ( k3_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X33 @ X34 ) @ ( k3_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('46',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X33 @ X34 ) @ ( k3_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('51',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ ( k5_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','55'])).

thf('57',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_xboole_0 @ X30 @ X31 )
      | ( ( k3_xboole_0 @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) )
        = ( k3_xboole_0 @ X30 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('60',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('62',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['32','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['31','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','72'])).

thf('74',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k2_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t99_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ) )).

thf('79',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X37 @ X38 ) @ X39 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X37 @ ( k2_xboole_0 @ X38 @ X39 ) ) @ ( k4_xboole_0 @ X38 @ ( k2_xboole_0 @ X37 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('84',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('85',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k5_xboole_0 @ k1_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ X35 @ ( k4_xboole_0 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('102',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['82','100','101','102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['77','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    sk_C
 != ( k5_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['2','106'])).

thf('108',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_xboole_0 @ X35 @ X36 )
      = ( k5_xboole_0 @ X35 @ ( k4_xboole_0 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf('110',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X37 @ X38 ) @ X39 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X37 @ ( k2_xboole_0 @ X38 @ X39 ) ) @ ( k4_xboole_0 @ X38 @ ( k2_xboole_0 @ X37 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[t99_xboole_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('113',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k5_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['108','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('117',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('120',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k3_xboole_0 @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['118','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('126',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('129',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k2_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['128','129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('132',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['124','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('136',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X1 ) ),
    inference(demod,[status(thm)],['115','136'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('140',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ ( k3_xboole_0 @ X13 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t23_xboole_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['138','143'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('146',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['82','100','101','102'])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k2_xboole_0 @ X33 @ X34 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X33 @ X34 ) @ ( k3_xboole_0 @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = X1 ) ),
    inference('sup+',[status(thm)],['138','143'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['139','140'])).

thf('156',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154','155','156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','16','17'])).

thf('160',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k2_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('161',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( k3_xboole_0 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X24 @ X25 ) @ ( k3_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X3 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ k1_xboole_0 ) @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['159','162'])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['96','99'])).

thf('165',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( k4_xboole_0 @ X27 @ ( k2_xboole_0 @ X28 @ X29 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X27 @ X28 ) @ ( k4_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t53_xboole_1])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X0 )
      = ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','132'])).

thf('167',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['163','164','165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ X0 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['158','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X1 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['137','168'])).

thf('170',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('171',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['169','170'])).

thf('172',plain,(
    sk_C
 != ( k4_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['107','171'])).

thf('173',plain,
    ( ( sk_C != sk_C )
    | ( r2_hidden @ sk_B @ sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['1','172'])).

thf('174',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(clc,[status(thm)],['174','175'])).

thf('177',plain,(
    $false ),
    inference(demod,[status(thm)],['0','176'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VTJKAqSJgq
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:36:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 6.72/6.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.72/6.90  % Solved by: fo/fo7.sh
% 6.72/6.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.72/6.90  % done 9348 iterations in 6.455s
% 6.72/6.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.72/6.90  % SZS output start Refutation
% 6.72/6.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.72/6.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.72/6.90  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 6.72/6.90  thf(sk_B_type, type, sk_B: $i).
% 6.72/6.90  thf(sk_C_type, type, sk_C: $i).
% 6.72/6.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.72/6.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.72/6.90  thf(sk_A_type, type, sk_A: $i).
% 6.72/6.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 6.72/6.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 6.72/6.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 6.72/6.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.72/6.90  thf(t145_zfmisc_1, conjecture,
% 6.72/6.90    (![A:$i,B:$i,C:$i]:
% 6.72/6.90     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 6.72/6.90          ( ( C ) !=
% 6.72/6.90            ( k4_xboole_0 @
% 6.72/6.90              ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 6.72/6.90              ( k2_tarski @ A @ B ) ) ) ) ))).
% 6.72/6.90  thf(zf_stmt_0, negated_conjecture,
% 6.72/6.90    (~( ![A:$i,B:$i,C:$i]:
% 6.72/6.90        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 6.72/6.90             ( ( C ) !=
% 6.72/6.90               ( k4_xboole_0 @
% 6.72/6.90                 ( k2_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) @ 
% 6.72/6.90                 ( k2_tarski @ A @ B ) ) ) ) ) )),
% 6.72/6.90    inference('cnf.neg', [status(esa)], [t145_zfmisc_1])).
% 6.72/6.90  thf('0', plain, (~ (r2_hidden @ sk_B @ sk_C)),
% 6.72/6.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.72/6.90  thf(t144_zfmisc_1, axiom,
% 6.72/6.90    (![A:$i,B:$i,C:$i]:
% 6.72/6.90     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 6.72/6.90          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 6.72/6.90  thf('1', plain,
% 6.72/6.90      (![X42 : $i, X43 : $i, X44 : $i]:
% 6.72/6.90         ((r2_hidden @ X42 @ X43)
% 6.72/6.90          | (r2_hidden @ X44 @ X43)
% 6.72/6.90          | ((X43) = (k4_xboole_0 @ X43 @ (k2_tarski @ X42 @ X44))))),
% 6.72/6.90      inference('cnf', [status(esa)], [t144_zfmisc_1])).
% 6.72/6.90  thf('2', plain,
% 6.72/6.90      (((sk_C)
% 6.72/6.90         != (k4_xboole_0 @ (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) @ 
% 6.72/6.90             (k2_tarski @ sk_A @ sk_B)))),
% 6.72/6.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.72/6.90  thf(t36_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 6.72/6.90  thf('3', plain,
% 6.72/6.90      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 6.72/6.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.72/6.90  thf(t3_xboole_1, axiom,
% 6.72/6.90    (![A:$i]:
% 6.72/6.90     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 6.72/6.90  thf('4', plain,
% 6.72/6.90      (![X20 : $i]:
% 6.72/6.90         (((X20) = (k1_xboole_0)) | ~ (r1_tarski @ X20 @ k1_xboole_0))),
% 6.72/6.90      inference('cnf', [status(esa)], [t3_xboole_1])).
% 6.72/6.90  thf('5', plain,
% 6.72/6.90      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.72/6.90      inference('sup-', [status(thm)], ['3', '4'])).
% 6.72/6.90  thf(t98_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i]:
% 6.72/6.90     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 6.72/6.90  thf('6', plain,
% 6.72/6.90      (![X35 : $i, X36 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X35 @ X36)
% 6.72/6.90           = (k5_xboole_0 @ X35 @ (k4_xboole_0 @ X36 @ X35)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.72/6.90  thf('7', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['5', '6'])).
% 6.72/6.90  thf(idempotence_k2_xboole_0, axiom,
% 6.72/6.90    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 6.72/6.90  thf('8', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 6.72/6.90      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 6.72/6.90  thf(t21_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 6.72/6.90  thf('9', plain,
% 6.72/6.90      (![X11 : $i, X12 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 6.72/6.90      inference('cnf', [status(esa)], [t21_xboole_1])).
% 6.72/6.90  thf('10', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['8', '9'])).
% 6.72/6.90  thf(t23_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i,C:$i]:
% 6.72/6.90     ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 6.72/6.90       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 6.72/6.90  thf('11', plain,
% 6.72/6.90      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 6.72/6.90           = (k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ 
% 6.72/6.90              (k3_xboole_0 @ X13 @ X15)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t23_xboole_1])).
% 6.72/6.90  thf('12', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 6.72/6.90           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['10', '11'])).
% 6.72/6.90  thf('13', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 6.72/6.90           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['7', '12'])).
% 6.72/6.90  thf('14', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['5', '6'])).
% 6.72/6.90  thf('15', plain,
% 6.72/6.90      (![X11 : $i, X12 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 6.72/6.90      inference('cnf', [status(esa)], [t21_xboole_1])).
% 6.72/6.90  thf('16', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['14', '15'])).
% 6.72/6.90  thf(t2_boole, axiom,
% 6.72/6.90    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 6.72/6.90  thf('17', plain,
% 6.72/6.90      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 6.72/6.90      inference('cnf', [status(esa)], [t2_boole])).
% 6.72/6.90  thf('18', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['13', '16', '17'])).
% 6.72/6.90  thf('19', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 6.72/6.90      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 6.72/6.90  thf('20', plain,
% 6.72/6.90      (![X18 : $i, X19 : $i]: (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X18)),
% 6.72/6.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 6.72/6.90  thf(t44_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i,C:$i]:
% 6.72/6.90     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 6.72/6.90       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 6.72/6.90  thf('21', plain,
% 6.72/6.90      (![X21 : $i, X22 : $i, X23 : $i]:
% 6.72/6.90         ((r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 6.72/6.90          | ~ (r1_tarski @ (k4_xboole_0 @ X21 @ X22) @ X23))),
% 6.72/6.90      inference('cnf', [status(esa)], [t44_xboole_1])).
% 6.72/6.90  thf('22', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 6.72/6.90      inference('sup-', [status(thm)], ['20', '21'])).
% 6.72/6.90  thf('23', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 6.72/6.90      inference('sup+', [status(thm)], ['19', '22'])).
% 6.72/6.90  thf(t106_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i,C:$i]:
% 6.72/6.90     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 6.72/6.90       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 6.72/6.90  thf('24', plain,
% 6.72/6.90      (![X1 : $i, X2 : $i, X3 : $i]:
% 6.72/6.90         ((r1_xboole_0 @ X1 @ X3)
% 6.72/6.90          | ~ (r1_tarski @ X1 @ (k4_xboole_0 @ X2 @ X3)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t106_xboole_1])).
% 6.72/6.90  thf('25', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 6.72/6.90      inference('sup-', [status(thm)], ['23', '24'])).
% 6.72/6.90  thf(t78_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i,C:$i]:
% 6.72/6.90     ( ( r1_xboole_0 @ A @ B ) =>
% 6.72/6.90       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 6.72/6.90         ( k3_xboole_0 @ A @ C ) ) ))).
% 6.72/6.90  thf('26', plain,
% 6.72/6.90      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.72/6.90         (~ (r1_xboole_0 @ X30 @ X31)
% 6.72/6.90          | ((k3_xboole_0 @ X30 @ (k2_xboole_0 @ X31 @ X32))
% 6.72/6.90              = (k3_xboole_0 @ X30 @ X32)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t78_xboole_1])).
% 6.72/6.90  thf('27', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k2_xboole_0 @ X0 @ X2))
% 6.72/6.90           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2))),
% 6.72/6.90      inference('sup-', [status(thm)], ['25', '26'])).
% 6.72/6.90  thf('28', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 6.72/6.90           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['18', '27'])).
% 6.72/6.90  thf('29', plain,
% 6.72/6.90      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 6.72/6.90      inference('cnf', [status(esa)], [t2_boole])).
% 6.72/6.90  thf('30', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['28', '29'])).
% 6.72/6.90  thf(t53_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i,C:$i]:
% 6.72/6.90     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 6.72/6.90       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 6.72/6.90  thf('31', plain,
% 6.72/6.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X27 @ (k2_xboole_0 @ X28 @ X29))
% 6.72/6.90           = (k3_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ 
% 6.72/6.90              (k4_xboole_0 @ X27 @ X29)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t53_xboole_1])).
% 6.72/6.90  thf('32', plain,
% 6.72/6.90      (![X35 : $i, X36 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X35 @ X36)
% 6.72/6.90           = (k5_xboole_0 @ X35 @ (k4_xboole_0 @ X36 @ X35)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.72/6.90  thf('33', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 6.72/6.90      inference('sup-', [status(thm)], ['20', '21'])).
% 6.72/6.90  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.72/6.90  thf('34', plain, (![X17 : $i]: (r1_tarski @ k1_xboole_0 @ X17)),
% 6.72/6.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.72/6.90  thf('35', plain,
% 6.72/6.90      (![X1 : $i, X2 : $i, X3 : $i]:
% 6.72/6.90         ((r1_xboole_0 @ X1 @ X3)
% 6.72/6.90          | ~ (r1_tarski @ X1 @ (k4_xboole_0 @ X2 @ X3)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t106_xboole_1])).
% 6.72/6.90  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 6.72/6.90      inference('sup-', [status(thm)], ['34', '35'])).
% 6.72/6.90  thf('37', plain,
% 6.72/6.90      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.72/6.90         (~ (r1_xboole_0 @ X30 @ X31)
% 6.72/6.90          | ((k3_xboole_0 @ X30 @ (k2_xboole_0 @ X31 @ X32))
% 6.72/6.90              = (k3_xboole_0 @ X30 @ X32)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t78_xboole_1])).
% 6.72/6.90  thf('38', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X1))
% 6.72/6.90           = (k3_xboole_0 @ k1_xboole_0 @ X1))),
% 6.72/6.90      inference('sup-', [status(thm)], ['36', '37'])).
% 6.72/6.90  thf('39', plain,
% 6.72/6.90      (![X11 : $i, X12 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 6.72/6.90      inference('cnf', [status(esa)], [t21_xboole_1])).
% 6.72/6.90  thf('40', plain,
% 6.72/6.90      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['38', '39'])).
% 6.72/6.90  thf(t93_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i]:
% 6.72/6.90     ( ( k2_xboole_0 @ A @ B ) =
% 6.72/6.90       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 6.72/6.90  thf('41', plain,
% 6.72/6.90      (![X33 : $i, X34 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X33 @ X34)
% 6.72/6.90           = (k2_xboole_0 @ (k5_xboole_0 @ X33 @ X34) @ 
% 6.72/6.90              (k3_xboole_0 @ X33 @ X34)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t93_xboole_1])).
% 6.72/6.90  thf('42', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 6.72/6.90           = (k2_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['40', '41'])).
% 6.72/6.90  thf('43', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['5', '6'])).
% 6.72/6.90  thf('44', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 6.72/6.90           = (k5_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['42', '43'])).
% 6.72/6.90  thf('45', plain,
% 6.72/6.90      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 6.72/6.90      inference('cnf', [status(esa)], [t2_boole])).
% 6.72/6.90  thf('46', plain,
% 6.72/6.90      (![X33 : $i, X34 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X33 @ X34)
% 6.72/6.90           = (k2_xboole_0 @ (k5_xboole_0 @ X33 @ X34) @ 
% 6.72/6.90              (k3_xboole_0 @ X33 @ X34)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t93_xboole_1])).
% 6.72/6.90  thf('47', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X0 @ k1_xboole_0)
% 6.72/6.90           = (k2_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['45', '46'])).
% 6.72/6.90  thf('48', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['5', '6'])).
% 6.72/6.90  thf('49', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['5', '6'])).
% 6.72/6.90  thf('50', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 6.72/6.90           = (k5_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['47', '48', '49'])).
% 6.72/6.90  thf(t107_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i,C:$i]:
% 6.72/6.90     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 6.72/6.90       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 6.72/6.90         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 6.72/6.90  thf('51', plain,
% 6.72/6.90      (![X4 : $i, X5 : $i, X6 : $i]:
% 6.72/6.90         ((r1_xboole_0 @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 6.72/6.90          | ~ (r1_tarski @ X4 @ (k5_xboole_0 @ X5 @ X6)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t107_xboole_1])).
% 6.72/6.90  thf('52', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 6.72/6.90          | (r1_xboole_0 @ X1 @ 
% 6.72/6.90             (k3_xboole_0 @ (k5_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)))),
% 6.72/6.90      inference('sup-', [status(thm)], ['50', '51'])).
% 6.72/6.90  thf('53', plain,
% 6.72/6.90      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 6.72/6.90      inference('cnf', [status(esa)], [t2_boole])).
% 6.72/6.90  thf('54', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         (~ (r1_tarski @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0))
% 6.72/6.90          | (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['52', '53'])).
% 6.72/6.90  thf('55', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         (~ (r1_tarski @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 6.72/6.90          | (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 6.72/6.90      inference('sup-', [status(thm)], ['44', '54'])).
% 6.72/6.90  thf('56', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 6.72/6.90      inference('sup-', [status(thm)], ['33', '55'])).
% 6.72/6.90  thf('57', plain,
% 6.72/6.90      (![X30 : $i, X31 : $i, X32 : $i]:
% 6.72/6.90         (~ (r1_xboole_0 @ X30 @ X31)
% 6.72/6.90          | ((k3_xboole_0 @ X30 @ (k2_xboole_0 @ X31 @ X32))
% 6.72/6.90              = (k3_xboole_0 @ X30 @ X32)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t78_xboole_1])).
% 6.72/6.90  thf('58', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 6.72/6.90           = (k3_xboole_0 @ X0 @ X1))),
% 6.72/6.90      inference('sup-', [status(thm)], ['56', '57'])).
% 6.72/6.90  thf('59', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ k1_xboole_0 @ X0)
% 6.72/6.90           = (k5_xboole_0 @ (k5_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['42', '43'])).
% 6.72/6.90  thf('60', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['13', '16', '17'])).
% 6.72/6.90  thf('61', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['5', '6'])).
% 6.72/6.90  thf('62', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['60', '61'])).
% 6.72/6.90  thf('63', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['59', '62'])).
% 6.72/6.90  thf('64', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1))
% 6.72/6.90           = (k3_xboole_0 @ X0 @ X1))),
% 6.72/6.90      inference('demod', [status(thm)], ['58', '63'])).
% 6.72/6.90  thf('65', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 6.72/6.90           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['32', '64'])).
% 6.72/6.90  thf('66', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['59', '62'])).
% 6.72/6.90  thf('67', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 6.72/6.90           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 6.72/6.90      inference('demod', [status(thm)], ['65', '66'])).
% 6.72/6.90  thf('68', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1))
% 6.72/6.90           = (k3_xboole_0 @ X0 @ X1))),
% 6.72/6.90      inference('demod', [status(thm)], ['58', '63'])).
% 6.72/6.90  thf('69', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X1 @ X0)
% 6.72/6.90           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 6.72/6.90      inference('demod', [status(thm)], ['67', '68'])).
% 6.72/6.90  thf('70', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 6.72/6.90           = (k4_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['31', '69'])).
% 6.72/6.90  thf('71', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['13', '16', '17'])).
% 6.72/6.90  thf('72', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 6.72/6.90           = (k4_xboole_0 @ X1 @ X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['70', '71'])).
% 6.72/6.90  thf('73', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['30', '72'])).
% 6.72/6.90  thf('74', plain,
% 6.72/6.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X27 @ (k2_xboole_0 @ X28 @ X29))
% 6.72/6.90           = (k3_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ 
% 6.72/6.90              (k4_xboole_0 @ X27 @ X29)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t53_xboole_1])).
% 6.72/6.90  thf('75', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 6.72/6.90           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['73', '74'])).
% 6.72/6.90  thf('76', plain,
% 6.72/6.90      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 6.72/6.90      inference('cnf', [status(esa)], [t2_boole])).
% 6.72/6.90  thf('77', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['75', '76'])).
% 6.72/6.90  thf('78', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['5', '6'])).
% 6.72/6.90  thf(t99_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i,C:$i]:
% 6.72/6.90     ( ( k4_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 6.72/6.90       ( k2_xboole_0 @
% 6.72/6.90         ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) @ 
% 6.72/6.90         ( k4_xboole_0 @ B @ ( k2_xboole_0 @ A @ C ) ) ) ))).
% 6.72/6.90  thf('79', plain,
% 6.72/6.90      (![X37 : $i, X38 : $i, X39 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ (k5_xboole_0 @ X37 @ X38) @ X39)
% 6.72/6.90           = (k2_xboole_0 @ (k4_xboole_0 @ X37 @ (k2_xboole_0 @ X38 @ X39)) @ 
% 6.72/6.90              (k4_xboole_0 @ X38 @ (k2_xboole_0 @ X37 @ X39))))),
% 6.72/6.90      inference('cnf', [status(esa)], [t99_xboole_1])).
% 6.72/6.90  thf('80', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 6.72/6.90           = (k2_xboole_0 @ 
% 6.72/6.90              (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 6.72/6.90              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ k1_xboole_0))))),
% 6.72/6.90      inference('sup+', [status(thm)], ['78', '79'])).
% 6.72/6.90  thf('81', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['5', '6'])).
% 6.72/6.90  thf('82', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 6.72/6.90           = (k2_xboole_0 @ 
% 6.72/6.90              (k4_xboole_0 @ X1 @ (k5_xboole_0 @ X0 @ k1_xboole_0)) @ 
% 6.72/6.90              (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ k1_xboole_0))))),
% 6.72/6.90      inference('demod', [status(thm)], ['80', '81'])).
% 6.72/6.90  thf('83', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['8', '9'])).
% 6.72/6.90  thf('84', plain,
% 6.72/6.90      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 6.72/6.90      inference('cnf', [status(esa)], [t2_boole])).
% 6.72/6.90  thf('85', plain,
% 6.72/6.90      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 6.72/6.90           = (k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ 
% 6.72/6.90              (k3_xboole_0 @ X13 @ X15)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t23_xboole_1])).
% 6.72/6.90  thf('86', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ k1_xboole_0 @ X0))
% 6.72/6.90           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['84', '85'])).
% 6.72/6.90  thf('87', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['59', '62'])).
% 6.72/6.90  thf('88', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['59', '62'])).
% 6.72/6.90  thf('89', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X1 @ (k5_xboole_0 @ k1_xboole_0 @ X0))
% 6.72/6.90           = (k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.72/6.90      inference('demod', [status(thm)], ['86', '87', '88'])).
% 6.72/6.90  thf('90', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ k1_xboole_0 @ X1))
% 6.72/6.90           = (k3_xboole_0 @ X0 @ X1))),
% 6.72/6.90      inference('demod', [status(thm)], ['58', '63'])).
% 6.72/6.90  thf('91', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k5_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0))
% 6.72/6.90           = (k3_xboole_0 @ X1 @ X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['89', '90'])).
% 6.72/6.90  thf('92', plain,
% 6.72/6.90      (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ X0 @ X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['83', '91'])).
% 6.72/6.90  thf('93', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['8', '9'])).
% 6.72/6.90  thf('94', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['92', '93'])).
% 6.72/6.90  thf('95', plain,
% 6.72/6.90      (![X35 : $i, X36 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X35 @ X36)
% 6.72/6.90           = (k5_xboole_0 @ X35 @ (k4_xboole_0 @ X36 @ X35)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.72/6.90  thf('96', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['94', '95'])).
% 6.72/6.90  thf('97', plain,
% 6.72/6.90      (![X0 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ k1_xboole_0 @ X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['59', '62'])).
% 6.72/6.90  thf('98', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['92', '93'])).
% 6.72/6.90  thf('99', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['97', '98'])).
% 6.72/6.90  thf('100', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['96', '99'])).
% 6.72/6.90  thf('101', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['60', '61'])).
% 6.72/6.90  thf('102', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['60', '61'])).
% 6.72/6.90  thf('103', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k5_xboole_0 @ X1 @ X0)
% 6.72/6.90           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 6.72/6.90      inference('demod', [status(thm)], ['82', '100', '101', '102'])).
% 6.72/6.90  thf('104', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 6.72/6.90           = (k2_xboole_0 @ k1_xboole_0 @ 
% 6.72/6.90              (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['77', '103'])).
% 6.72/6.90  thf('105', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['97', '98'])).
% 6.72/6.90  thf('106', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 6.72/6.90           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['104', '105'])).
% 6.72/6.90  thf('107', plain,
% 6.72/6.90      (((sk_C)
% 6.72/6.90         != (k5_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ 
% 6.72/6.90             (k2_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))))),
% 6.72/6.90      inference('demod', [status(thm)], ['2', '106'])).
% 6.72/6.90  thf('108', plain,
% 6.72/6.90      (![X35 : $i, X36 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X35 @ X36)
% 6.72/6.90           = (k5_xboole_0 @ X35 @ (k4_xboole_0 @ X36 @ X35)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 6.72/6.90  thf('109', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 6.72/6.90      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 6.72/6.90  thf('110', plain,
% 6.72/6.90      (![X37 : $i, X38 : $i, X39 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ (k5_xboole_0 @ X37 @ X38) @ X39)
% 6.72/6.90           = (k2_xboole_0 @ (k4_xboole_0 @ X37 @ (k2_xboole_0 @ X38 @ X39)) @ 
% 6.72/6.90              (k4_xboole_0 @ X38 @ (k2_xboole_0 @ X37 @ X39))))),
% 6.72/6.90      inference('cnf', [status(esa)], [t99_xboole_1])).
% 6.72/6.90  thf('111', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0)
% 6.72/6.90           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ 
% 6.72/6.90              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))))),
% 6.72/6.90      inference('sup+', [status(thm)], ['109', '110'])).
% 6.72/6.90  thf('112', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['75', '76'])).
% 6.72/6.90  thf('113', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['13', '16', '17'])).
% 6.72/6.90  thf('114', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ (k5_xboole_0 @ X1 @ X0) @ X0)
% 6.72/6.90           = (k4_xboole_0 @ X1 @ X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['111', '112', '113'])).
% 6.72/6.90  thf('115', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 6.72/6.90           = (k4_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['108', '114'])).
% 6.72/6.90  thf('116', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['8', '9'])).
% 6.72/6.90  thf(t50_xboole_1, axiom,
% 6.72/6.90    (![A:$i,B:$i,C:$i]:
% 6.72/6.90     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 6.72/6.90       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 6.72/6.90  thf('117', plain,
% 6.72/6.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 6.72/6.90           = (k4_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 6.72/6.90              (k3_xboole_0 @ X24 @ X26)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t50_xboole_1])).
% 6.72/6.90  thf('118', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 6.72/6.90           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['116', '117'])).
% 6.72/6.90  thf('119', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X0 @ X1))
% 6.72/6.90           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['10', '11'])).
% 6.72/6.90  thf('120', plain,
% 6.72/6.90      (![X11 : $i, X12 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X11 @ (k2_xboole_0 @ X11 @ X12)) = (X11))),
% 6.72/6.90      inference('cnf', [status(esa)], [t21_xboole_1])).
% 6.72/6.90  thf('121', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 6.72/6.90      inference('sup+', [status(thm)], ['119', '120'])).
% 6.72/6.90  thf('122', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['75', '76'])).
% 6.72/6.90  thf('123', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['121', '122'])).
% 6.72/6.90  thf('124', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['118', '123'])).
% 6.72/6.90  thf('125', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['8', '9'])).
% 6.72/6.90  thf('126', plain,
% 6.72/6.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 6.72/6.90           = (k4_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 6.72/6.90              (k3_xboole_0 @ X24 @ X26)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t50_xboole_1])).
% 6.72/6.90  thf('127', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 6.72/6.90           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['125', '126'])).
% 6.72/6.90  thf('128', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['96', '99'])).
% 6.72/6.90  thf('129', plain,
% 6.72/6.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X27 @ (k2_xboole_0 @ X28 @ X29))
% 6.72/6.90           = (k3_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ 
% 6.72/6.90              (k4_xboole_0 @ X27 @ X29)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t53_xboole_1])).
% 6.72/6.90  thf('130', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1))
% 6.72/6.90           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['128', '129'])).
% 6.72/6.90  thf('131', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['97', '98'])).
% 6.72/6.90  thf('132', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ X1)
% 6.72/6.90           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 6.72/6.90      inference('demod', [status(thm)], ['130', '131'])).
% 6.72/6.90  thf('133', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X1 @ X0)
% 6.72/6.90           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['127', '132'])).
% 6.72/6.90  thf('134', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 6.72/6.90           = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['124', '133'])).
% 6.72/6.90  thf('135', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['96', '99'])).
% 6.72/6.90  thf('136', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['134', '135'])).
% 6.72/6.90  thf('137', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 6.72/6.90           = (X1))),
% 6.72/6.90      inference('demod', [status(thm)], ['115', '136'])).
% 6.72/6.90  thf('138', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ X1)
% 6.72/6.90           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 6.72/6.90      inference('demod', [status(thm)], ['130', '131'])).
% 6.72/6.90  thf('139', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['8', '9'])).
% 6.72/6.90  thf('140', plain,
% 6.72/6.90      (![X13 : $i, X14 : $i, X15 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 6.72/6.90           = (k2_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ 
% 6.72/6.90              (k3_xboole_0 @ X13 @ X15)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t23_xboole_1])).
% 6.72/6.90  thf('141', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 6.72/6.90           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['139', '140'])).
% 6.72/6.90  thf('142', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) = (X1))),
% 6.72/6.90      inference('sup+', [status(thm)], ['119', '120'])).
% 6.72/6.90  thf('143', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))
% 6.72/6.90           = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['141', '142'])).
% 6.72/6.90  thf('144', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))
% 6.72/6.90           = (X1))),
% 6.72/6.90      inference('sup+', [status(thm)], ['138', '143'])).
% 6.72/6.90  thf('145', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['75', '76'])).
% 6.72/6.90  thf('146', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) @ X0)
% 6.72/6.90           = (k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['144', '145'])).
% 6.72/6.90  thf('147', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k5_xboole_0 @ X1 @ X0)
% 6.72/6.90           = (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 6.72/6.90      inference('demod', [status(thm)], ['82', '100', '101', '102'])).
% 6.72/6.90  thf('148', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 6.72/6.90           = (k2_xboole_0 @ 
% 6.72/6.90              (k4_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)) @ 
% 6.72/6.90              k1_xboole_0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['146', '147'])).
% 6.72/6.90  thf('149', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['75', '76'])).
% 6.72/6.90  thf('150', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['97', '98'])).
% 6.72/6.90  thf('151', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 6.72/6.90           = (k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['148', '149', '150'])).
% 6.72/6.90  thf('152', plain,
% 6.72/6.90      (![X33 : $i, X34 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X33 @ X34)
% 6.72/6.90           = (k2_xboole_0 @ (k5_xboole_0 @ X33 @ X34) @ 
% 6.72/6.90              (k3_xboole_0 @ X33 @ X34)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t93_xboole_1])).
% 6.72/6.90  thf('153', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 6.72/6.90           = (k2_xboole_0 @ k1_xboole_0 @ 
% 6.72/6.90              (k3_xboole_0 @ X0 @ (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))))),
% 6.72/6.90      inference('sup+', [status(thm)], ['151', '152'])).
% 6.72/6.90  thf('154', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))
% 6.72/6.90           = (X1))),
% 6.72/6.90      inference('sup+', [status(thm)], ['138', '143'])).
% 6.72/6.90  thf('155', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 6.72/6.90           = (k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['139', '140'])).
% 6.72/6.90  thf('156', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X0 @ X1)
% 6.72/6.90           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 6.72/6.90      inference('demod', [status(thm)], ['130', '131'])).
% 6.72/6.90  thf('157', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['97', '98'])).
% 6.72/6.90  thf('158', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((X0) = (k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['153', '154', '155', '156', '157'])).
% 6.72/6.90  thf('159', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 6.72/6.90      inference('demod', [status(thm)], ['13', '16', '17'])).
% 6.72/6.90  thf('160', plain,
% 6.72/6.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X27 @ (k2_xboole_0 @ X28 @ X29))
% 6.72/6.90           = (k3_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ 
% 6.72/6.90              (k4_xboole_0 @ X27 @ X29)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t53_xboole_1])).
% 6.72/6.90  thf('161', plain,
% 6.72/6.90      (![X24 : $i, X25 : $i, X26 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 6.72/6.90           = (k4_xboole_0 @ (k3_xboole_0 @ X24 @ X25) @ 
% 6.72/6.90              (k3_xboole_0 @ X24 @ X26)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t50_xboole_1])).
% 6.72/6.90  thf('162', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ 
% 6.72/6.90           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X3))
% 6.72/6.90           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ 
% 6.72/6.90              (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X3)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['160', '161'])).
% 6.72/6.90  thf('163', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.72/6.90         ((k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 6.72/6.90           (k4_xboole_0 @ (k4_xboole_0 @ X2 @ k1_xboole_0) @ X1))
% 6.72/6.90           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 6.72/6.90              (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['159', '162'])).
% 6.72/6.90  thf('164', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['96', '99'])).
% 6.72/6.90  thf('165', plain,
% 6.72/6.90      (![X27 : $i, X28 : $i, X29 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X27 @ (k2_xboole_0 @ X28 @ X29))
% 6.72/6.90           = (k3_xboole_0 @ (k4_xboole_0 @ X27 @ X28) @ 
% 6.72/6.90              (k4_xboole_0 @ X27 @ X29)))),
% 6.72/6.90      inference('cnf', [status(esa)], [t53_xboole_1])).
% 6.72/6.90  thf('166', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X1 @ X0)
% 6.72/6.90           = (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 6.72/6.90      inference('sup+', [status(thm)], ['127', '132'])).
% 6.72/6.90  thf('167', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X0 @ X1))
% 6.72/6.90           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1))),
% 6.72/6.90      inference('demod', [status(thm)], ['163', '164', '165', '166'])).
% 6.72/6.90  thf('168', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ X2 @ X0)
% 6.72/6.90           = (k4_xboole_0 @ (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1)) @ X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['158', '167'])).
% 6.72/6.90  thf('169', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X1)
% 6.72/6.90           = (k4_xboole_0 @ X0 @ X1))),
% 6.72/6.90      inference('sup+', [status(thm)], ['137', '168'])).
% 6.72/6.90  thf('170', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 6.72/6.90           = (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0))),
% 6.72/6.90      inference('demod', [status(thm)], ['104', '105'])).
% 6.72/6.90  thf('171', plain,
% 6.72/6.90      (![X0 : $i, X1 : $i]:
% 6.72/6.90         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 6.72/6.90           = (k4_xboole_0 @ X1 @ X0))),
% 6.72/6.90      inference('sup+', [status(thm)], ['169', '170'])).
% 6.72/6.90  thf('172', plain,
% 6.72/6.90      (((sk_C) != (k4_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)))),
% 6.72/6.90      inference('demod', [status(thm)], ['107', '171'])).
% 6.72/6.90  thf('173', plain,
% 6.72/6.90      ((((sk_C) != (sk_C))
% 6.72/6.90        | (r2_hidden @ sk_B @ sk_C)
% 6.72/6.90        | (r2_hidden @ sk_A @ sk_C))),
% 6.72/6.90      inference('sup-', [status(thm)], ['1', '172'])).
% 6.72/6.90  thf('174', plain, (((r2_hidden @ sk_A @ sk_C) | (r2_hidden @ sk_B @ sk_C))),
% 6.72/6.90      inference('simplify', [status(thm)], ['173'])).
% 6.72/6.90  thf('175', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 6.72/6.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.72/6.90  thf('176', plain, ((r2_hidden @ sk_B @ sk_C)),
% 6.72/6.90      inference('clc', [status(thm)], ['174', '175'])).
% 6.72/6.90  thf('177', plain, ($false), inference('demod', [status(thm)], ['0', '176'])).
% 6.72/6.90  
% 6.72/6.90  % SZS output end Refutation
% 6.72/6.90  
% 6.72/6.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
