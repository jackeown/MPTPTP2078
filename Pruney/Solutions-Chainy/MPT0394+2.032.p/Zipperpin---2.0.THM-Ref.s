%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zv1aaNjG9c

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:49 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  101 (1714 expanded)
%              Number of leaves         :   21 ( 524 expanded)
%              Depth                    :   20
%              Number of atoms          :  705 (15171 expanded)
%              Number of equality atoms :  114 (1708 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_tarski @ X16 @ X17 )
      = ( k2_xboole_0 @ ( k1_tarski @ X16 ) @ ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('2',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X21 ) @ ( k1_setfam_1 @ X22 ) ) )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t18_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X19 ) )
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t18_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
       != ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_B = X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('15',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ( ( k3_xboole_0 @ X6 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('23',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('26',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k3_xboole_0 @ X10 @ X13 ) )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('35',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['16','35'])).

thf('37',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( sk_B = X0 ) ) ),
    inference(demod,[status(thm)],['12','38'])).

thf('40',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(eq_fact,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( sk_B = X0 )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X19 ) )
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t18_zfmisc_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
       != ( k1_tarski @ sk_A ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('48',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['42','43'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('51',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('52',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['42','43'])).

thf('53',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('54',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('55',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('56',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X19 ) )
       != ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t18_zfmisc_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
       != ( k1_tarski @ sk_A ) )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ sk_A ) )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B )
      | ( sk_A = X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X18: $i] :
      ( ( k2_tarski @ X18 @ X18 )
      = ( k1_tarski @ X18 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('64',plain,(
    ! [X23: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X23 ) )
      = X23 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( sk_A = X0 )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('67',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ sk_B ) )
       != ( k3_xboole_0 @ sk_A @ sk_B ) )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_B
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k3_xboole_0 @ X0 @ sk_B ) )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B )
      | ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k1_setfam_1 @ k1_xboole_0 )
        = sk_B )
      | ( sk_B
       != ( k3_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( sk_B != sk_B )
    | ( ( k1_setfam_1 @ k1_xboole_0 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['53','71'])).

thf('73',plain,
    ( ( k1_setfam_1 @ k1_xboole_0 )
    = sk_B ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('75',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('76',plain,(
    ! [X9: $i] :
      ( ( k3_xboole_0 @ X9 @ X9 )
      = X9 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('77',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','50','51','52','73','74','75','76'])).

thf('78',plain,(
    $false ),
    inference(simplify,[status(thm)],['77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zv1aaNjG9c
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:59:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 233 iterations in 0.177s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.64  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.45/0.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.45/0.64  thf(t12_setfam_1, conjecture,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i,B:$i]:
% 0.45/0.64        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.45/0.64         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(t41_enumset1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( k2_tarski @ A @ B ) =
% 0.45/0.64       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.45/0.64  thf('1', plain,
% 0.45/0.64      (![X16 : $i, X17 : $i]:
% 0.45/0.64         ((k2_tarski @ X16 @ X17)
% 0.45/0.64           = (k2_xboole_0 @ (k1_tarski @ X16) @ (k1_tarski @ X17)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.45/0.64  thf(t11_setfam_1, axiom,
% 0.45/0.64    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.45/0.64  thf('2', plain, (![X23 : $i]: ((k1_setfam_1 @ (k1_tarski @ X23)) = (X23))),
% 0.45/0.64      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.64  thf(t10_setfam_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.45/0.64          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.45/0.64            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X21 : $i, X22 : $i]:
% 0.45/0.64         (((X21) = (k1_xboole_0))
% 0.45/0.64          | ((k1_setfam_1 @ (k2_xboole_0 @ X21 @ X22))
% 0.45/0.64              = (k3_xboole_0 @ (k1_setfam_1 @ X21) @ (k1_setfam_1 @ X22)))
% 0.45/0.64          | ((X22) = (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.45/0.64  thf('4', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (((k1_setfam_1 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.45/0.64            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.45/0.64          | ((X1) = (k1_xboole_0))
% 0.45/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['2', '3'])).
% 0.45/0.64  thf('5', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.45/0.64            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.45/0.64          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.45/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup+', [status(thm)], ['1', '4'])).
% 0.45/0.64  thf('6', plain, (![X23 : $i]: ((k1_setfam_1 @ (k1_tarski @ X23)) = (X23))),
% 0.45/0.64      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.64  thf('7', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.45/0.64          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.45/0.64          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['5', '6'])).
% 0.45/0.64  thf('8', plain,
% 0.45/0.64      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.45/0.64         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.45/0.64        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.45/0.64        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.64        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.45/0.64      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.64  thf(t18_zfmisc_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.64         ( k1_tarski @ A ) ) =>
% 0.45/0.64       ( ( A ) = ( B ) ) ))).
% 0.45/0.64  thf('11', plain,
% 0.45/0.65      (![X19 : $i, X20 : $i]:
% 0.45/0.65         (((X20) = (X19))
% 0.45/0.65          | ((k3_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X19))
% 0.45/0.65              != (k1_tarski @ X20)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t18_zfmisc_1])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) != (k1_tarski @ sk_B))
% 0.45/0.65          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.65          | ((sk_B) = (X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.65  thf(t4_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.65       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.65            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X10 @ X11)
% 0.45/0.65          | (r2_hidden @ (sk_C @ X11 @ X10) @ (k3_xboole_0 @ X10 @ X11)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf(d4_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.45/0.65       ( ![D:$i]:
% 0.45/0.65         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.65           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X4 @ X3)
% 0.45/0.65          | (r2_hidden @ X4 @ X1)
% 0.45/0.65          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.45/0.65         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['13', '15'])).
% 0.45/0.65  thf(idempotence_k3_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.45/0.65  thf('17', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.65  thf(d7_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.45/0.65       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X6 : $i, X8 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X6 @ X8) | ((k3_xboole_0 @ X6 @ X8) != (k1_xboole_0)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X0 : $i]: (((X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.65  thf('20', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.45/0.65      inference('simplify', [status(thm)], ['19'])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X10 : $i, X11 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X10 @ X11)
% 0.45/0.65          | (r2_hidden @ (sk_C @ X11 @ X10) @ (k3_xboole_0 @ X10 @ X11)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X4 @ X3)
% 0.45/0.65          | (r2_hidden @ X4 @ X2)
% 0.45/0.65          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.45/0.65         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['21', '23'])).
% 0.45/0.65  thf('25', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.45/0.65          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.65  thf('28', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_xboole_0 @ X0 @ X0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['24', '27'])).
% 0.45/0.65  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('sup-', [status(thm)], ['20', '28'])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X6 : $i, X7 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X12 @ (k3_xboole_0 @ X10 @ X13))
% 0.45/0.65          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.45/0.65      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.65  thf('34', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.45/0.65      inference('sup-', [status(thm)], ['20', '28'])).
% 0.45/0.65  thf('35', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.45/0.65      inference('demod', [status(thm)], ['33', '34'])).
% 0.45/0.65  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.65      inference('sup-', [status(thm)], ['16', '35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (![X6 : $i, X7 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.45/0.65      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k1_xboole_0) != (k1_tarski @ sk_B))
% 0.45/0.65          | ((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.65          | ((sk_B) = (X0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['12', '38'])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.65        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (![X0 : $i]: (((sk_B) = (X0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.65      inference('clc', [status(thm)], ['39', '40'])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      ((((sk_B) != (k1_xboole_0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.65      inference('eq_fact', [status(thm)], ['41'])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      (![X0 : $i]: (((sk_B) = (X0)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.65      inference('clc', [status(thm)], ['39', '40'])).
% 0.45/0.65  thf('44', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('clc', [status(thm)], ['42', '43'])).
% 0.45/0.65  thf('45', plain,
% 0.45/0.65      (![X19 : $i, X20 : $i]:
% 0.45/0.65         (((X20) = (X19))
% 0.45/0.65          | ((k3_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X19))
% 0.45/0.65              != (k1_tarski @ X20)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t18_zfmisc_1])).
% 0.45/0.65  thf('46', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) != (k1_tarski @ sk_A))
% 0.45/0.65          | ((sk_A) = (X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.65  thf('47', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.65  thf('48', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('clc', [status(thm)], ['42', '43'])).
% 0.45/0.65  thf('49', plain,
% 0.45/0.65      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (X0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.45/0.65  thf('50', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['49'])).
% 0.45/0.65  thf(t69_enumset1, axiom,
% 0.45/0.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.65  thf('51', plain,
% 0.45/0.65      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.65  thf('52', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.45/0.65      inference('clc', [status(thm)], ['42', '43'])).
% 0.45/0.65  thf('53', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.65  thf('54', plain,
% 0.45/0.65      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.45/0.65        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.65  thf('55', plain, (![X23 : $i]: ((k1_setfam_1 @ (k1_tarski @ X23)) = (X23))),
% 0.45/0.65      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.65  thf('56', plain,
% 0.45/0.65      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.45/0.65        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['54', '55'])).
% 0.45/0.65  thf('57', plain,
% 0.45/0.65      (![X19 : $i, X20 : $i]:
% 0.45/0.65         (((X20) = (X19))
% 0.45/0.65          | ((k3_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X19))
% 0.45/0.65              != (k1_tarski @ X20)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t18_zfmisc_1])).
% 0.45/0.65  thf('58', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) != (k1_tarski @ sk_A))
% 0.45/0.65          | ((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.45/0.65          | ((sk_A) = (X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['56', '57'])).
% 0.45/0.65  thf('59', plain,
% 0.45/0.65      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.65      inference('sup-', [status(thm)], ['36', '37'])).
% 0.45/0.65  thf('60', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k1_xboole_0) != (k1_tarski @ sk_A))
% 0.45/0.65          | ((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.45/0.65          | ((sk_A) = (X0)))),
% 0.45/0.65      inference('demod', [status(thm)], ['58', '59'])).
% 0.45/0.65  thf('61', plain,
% 0.45/0.65      ((((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.45/0.65        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.45/0.65      inference('sup+', [status(thm)], ['54', '55'])).
% 0.45/0.65  thf('62', plain,
% 0.45/0.65      (![X0 : $i]: (((sk_A) = (X0)) | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.45/0.65      inference('clc', [status(thm)], ['60', '61'])).
% 0.45/0.65  thf('63', plain,
% 0.45/0.65      (![X18 : $i]: ((k2_tarski @ X18 @ X18) = (k1_tarski @ X18))),
% 0.45/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.65  thf('64', plain, (![X23 : $i]: ((k1_setfam_1 @ (k1_tarski @ X23)) = (X23))),
% 0.45/0.65      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.45/0.65  thf('65', plain,
% 0.45/0.65      (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['63', '64'])).
% 0.45/0.65  thf('66', plain,
% 0.45/0.65      (![X0 : $i]: (((sk_A) = (X0)) | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.45/0.65      inference('clc', [status(thm)], ['60', '61'])).
% 0.45/0.65  thf('67', plain,
% 0.45/0.65      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.45/0.65         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('68', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k1_setfam_1 @ (k2_tarski @ X0 @ sk_B))
% 0.45/0.65            != (k3_xboole_0 @ sk_A @ sk_B))
% 0.45/0.65          | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['66', '67'])).
% 0.45/0.65  thf('69', plain,
% 0.45/0.65      ((((sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.45/0.65        | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['65', '68'])).
% 0.45/0.65  thf('70', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((sk_B) != (k3_xboole_0 @ X0 @ sk_B))
% 0.45/0.65          | ((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.45/0.65          | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['62', '69'])).
% 0.45/0.65  thf('71', plain,
% 0.45/0.65      (![X0 : $i]:
% 0.45/0.65         (((k1_setfam_1 @ k1_xboole_0) = (sk_B))
% 0.45/0.65          | ((sk_B) != (k3_xboole_0 @ X0 @ sk_B)))),
% 0.45/0.65      inference('simplify', [status(thm)], ['70'])).
% 0.45/0.65  thf('72', plain,
% 0.45/0.65      ((((sk_B) != (sk_B)) | ((k1_setfam_1 @ k1_xboole_0) = (sk_B)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['53', '71'])).
% 0.45/0.65  thf('73', plain, (((k1_setfam_1 @ k1_xboole_0) = (sk_B))),
% 0.45/0.65      inference('simplify', [status(thm)], ['72'])).
% 0.45/0.65  thf('74', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['49'])).
% 0.45/0.65  thf('75', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['49'])).
% 0.45/0.65  thf('76', plain, (![X9 : $i]: ((k3_xboole_0 @ X9 @ X9) = (X9))),
% 0.45/0.65      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.45/0.65  thf('77', plain, (((sk_A) != (sk_A))),
% 0.45/0.65      inference('demod', [status(thm)],
% 0.45/0.65                ['0', '50', '51', '52', '73', '74', '75', '76'])).
% 0.45/0.65  thf('78', plain, ($false), inference('simplify', [status(thm)], ['77'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
