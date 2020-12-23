%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pHVmkxcbzE

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:44 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 131 expanded)
%              Number of leaves         :   21 (  44 expanded)
%              Depth                    :   16
%              Number of atoms          :  524 (1023 expanded)
%              Number of equality atoms :   51 (  89 expanded)
%              Maximal formula depth    :   11 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X34 @ X33 ) @ X33 )
      | ( r1_tarski @ X34 @ ( k1_setfam_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X28 ) )
        = ( k1_tarski @ X27 ) )
      | ( X27 = X28 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29 != X31 )
      | ~ ( r2_hidden @ X29 @ ( k4_xboole_0 @ X30 @ ( k1_tarski @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('4',plain,(
    ! [X30: $i,X31: $i] :
      ~ ( r2_hidden @ X31 @ ( k4_xboole_0 @ X30 @ ( k1_tarski @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27 != X26 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X27 ) @ ( k1_tarski @ X26 ) )
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('8',plain,(
    ! [X26: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X26 ) @ ( k1_tarski @ X26 ) )
     != ( k1_tarski @ X26 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ( r2_hidden @ X8 @ X5 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('11',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r2_hidden @ X8 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X0 ) @ X1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X13: $i] :
      ( ( k4_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('21',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X26: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X26 ) ) ),
    inference(demod,[status(thm)],['8','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['6','28'])).

thf('30',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('31',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('32',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('33',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( X15 != X14 )
      | ( r2_hidden @ X15 @ X16 )
      | ( X16
       != ( k2_tarski @ X17 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('34',plain,(
    ! [X14: $i,X17: $i] :
      ( r2_hidden @ X14 @ ( k2_tarski @ X17 @ X14 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('36',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X35 @ X36 )
      | ~ ( r1_tarski @ X35 @ X37 )
      | ( r1_tarski @ ( k1_setfam_1 @ X36 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    ! [X10: $i,X12: $i] :
      ( ( X10 = X12 )
      | ~ ( r1_tarski @ X12 @ X10 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X33 = k1_xboole_0 )
      | ~ ( r1_tarski @ X34 @ ( sk_C_1 @ X34 @ X33 ) )
      | ( r1_tarski @ X34 @ ( k1_setfam_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X26: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X26 ) ) ),
    inference(demod,[status(thm)],['8','27'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pHVmkxcbzE
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:00:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.99/1.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.20  % Solved by: fo/fo7.sh
% 0.99/1.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.20  % done 705 iterations in 0.743s
% 0.99/1.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.20  % SZS output start Refutation
% 0.99/1.20  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.99/1.20  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.99/1.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.20  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.20  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.99/1.20  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.99/1.20  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.99/1.20  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.99/1.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.20  thf(t11_setfam_1, conjecture,
% 0.99/1.20    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.99/1.20  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.20    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.99/1.20    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.99/1.20  thf('0', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.99/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.20  thf(t6_setfam_1, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.99/1.20       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.99/1.20  thf('1', plain,
% 0.99/1.20      (![X33 : $i, X34 : $i]:
% 0.99/1.20         (((X33) = (k1_xboole_0))
% 0.99/1.20          | (r2_hidden @ (sk_C_1 @ X34 @ X33) @ X33)
% 0.99/1.20          | (r1_tarski @ X34 @ (k1_setfam_1 @ X33)))),
% 0.99/1.20      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.99/1.20  thf(t20_zfmisc_1, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.99/1.20         ( k1_tarski @ A ) ) <=>
% 0.99/1.20       ( ( A ) != ( B ) ) ))).
% 0.99/1.20  thf('2', plain,
% 0.99/1.20      (![X27 : $i, X28 : $i]:
% 0.99/1.20         (((k4_xboole_0 @ (k1_tarski @ X27) @ (k1_tarski @ X28))
% 0.99/1.20            = (k1_tarski @ X27))
% 0.99/1.20          | ((X27) = (X28)))),
% 0.99/1.20      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.99/1.20  thf(t64_zfmisc_1, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.99/1.20       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.99/1.20  thf('3', plain,
% 0.99/1.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.99/1.20         (((X29) != (X31))
% 0.99/1.20          | ~ (r2_hidden @ X29 @ (k4_xboole_0 @ X30 @ (k1_tarski @ X31))))),
% 0.99/1.20      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.99/1.20  thf('4', plain,
% 0.99/1.20      (![X30 : $i, X31 : $i]:
% 0.99/1.20         ~ (r2_hidden @ X31 @ (k4_xboole_0 @ X30 @ (k1_tarski @ X31)))),
% 0.99/1.20      inference('simplify', [status(thm)], ['3'])).
% 0.99/1.20  thf('5', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['2', '4'])).
% 0.99/1.20  thf('6', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.99/1.20          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.99/1.20          | ((X0) = (sk_C_1 @ X1 @ (k1_tarski @ X0))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['1', '5'])).
% 0.99/1.20  thf('7', plain,
% 0.99/1.20      (![X26 : $i, X27 : $i]:
% 0.99/1.20         (((X27) != (X26))
% 0.99/1.20          | ((k4_xboole_0 @ (k1_tarski @ X27) @ (k1_tarski @ X26))
% 0.99/1.20              != (k1_tarski @ X27)))),
% 0.99/1.20      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.99/1.20  thf('8', plain,
% 0.99/1.20      (![X26 : $i]:
% 0.99/1.20         ((k4_xboole_0 @ (k1_tarski @ X26) @ (k1_tarski @ X26))
% 0.99/1.20           != (k1_tarski @ X26))),
% 0.99/1.20      inference('simplify', [status(thm)], ['7'])).
% 0.99/1.20  thf(d3_tarski, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( r1_tarski @ A @ B ) <=>
% 0.99/1.20       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.99/1.20  thf('9', plain,
% 0.99/1.20      (![X1 : $i, X3 : $i]:
% 0.99/1.20         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_tarski])).
% 0.99/1.20  thf(d5_xboole_0, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.99/1.20       ( ![D:$i]:
% 0.99/1.20         ( ( r2_hidden @ D @ C ) <=>
% 0.99/1.20           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.99/1.20  thf('10', plain,
% 0.99/1.20      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.99/1.20         (~ (r2_hidden @ X8 @ X7)
% 0.99/1.20          | (r2_hidden @ X8 @ X5)
% 0.99/1.20          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.99/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.99/1.20  thf('11', plain,
% 0.99/1.20      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.99/1.20         ((r2_hidden @ X8 @ X5) | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.99/1.20      inference('simplify', [status(thm)], ['10'])).
% 0.99/1.20  thf('12', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.20         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.99/1.20          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['9', '11'])).
% 0.99/1.20  thf('13', plain,
% 0.99/1.20      (![X1 : $i, X3 : $i]:
% 0.99/1.20         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_tarski])).
% 0.99/1.20  thf('14', plain,
% 0.99/1.20      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.99/1.20         (~ (r2_hidden @ X8 @ X7)
% 0.99/1.20          | ~ (r2_hidden @ X8 @ X6)
% 0.99/1.20          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.99/1.20      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.99/1.20  thf('15', plain,
% 0.99/1.20      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.99/1.20         (~ (r2_hidden @ X8 @ X6)
% 0.99/1.20          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.99/1.20      inference('simplify', [status(thm)], ['14'])).
% 0.99/1.20  thf('16', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.20         ((r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.99/1.20          | ~ (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['13', '15'])).
% 0.99/1.20  thf('17', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)
% 0.99/1.20          | (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['12', '16'])).
% 0.99/1.20  thf('18', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X0) @ X1)),
% 0.99/1.20      inference('simplify', [status(thm)], ['17'])).
% 0.99/1.20  thf('19', plain,
% 0.99/1.20      (![X1 : $i, X3 : $i]:
% 0.99/1.20         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.99/1.20      inference('cnf', [status(esa)], [d3_tarski])).
% 0.99/1.20  thf(t3_boole, axiom,
% 0.99/1.20    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.99/1.20  thf('20', plain, (![X13 : $i]: ((k4_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.99/1.20      inference('cnf', [status(esa)], [t3_boole])).
% 0.99/1.20  thf('21', plain,
% 0.99/1.20      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.99/1.20         (~ (r2_hidden @ X8 @ X6)
% 0.99/1.20          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.99/1.20      inference('simplify', [status(thm)], ['14'])).
% 0.99/1.20  thf('22', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['20', '21'])).
% 0.99/1.20  thf('23', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.99/1.20      inference('condensation', [status(thm)], ['22'])).
% 0.99/1.20  thf('24', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.99/1.20      inference('sup-', [status(thm)], ['19', '23'])).
% 0.99/1.20  thf(d10_xboole_0, axiom,
% 0.99/1.20    (![A:$i,B:$i]:
% 0.99/1.20     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.99/1.20  thf('25', plain,
% 0.99/1.20      (![X10 : $i, X12 : $i]:
% 0.99/1.20         (((X10) = (X12))
% 0.99/1.20          | ~ (r1_tarski @ X12 @ X10)
% 0.99/1.20          | ~ (r1_tarski @ X10 @ X12))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('26', plain,
% 0.99/1.20      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['24', '25'])).
% 0.99/1.20  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.99/1.20      inference('sup-', [status(thm)], ['18', '26'])).
% 0.99/1.20  thf('28', plain, (![X26 : $i]: ((k1_xboole_0) != (k1_tarski @ X26))),
% 0.99/1.20      inference('demod', [status(thm)], ['8', '27'])).
% 0.99/1.20  thf('29', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         (((X0) = (sk_C_1 @ X1 @ (k1_tarski @ X0)))
% 0.99/1.20          | (r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.99/1.20      inference('clc', [status(thm)], ['6', '28'])).
% 0.99/1.20  thf('30', plain,
% 0.99/1.20      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('31', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.99/1.20      inference('simplify', [status(thm)], ['30'])).
% 0.99/1.20  thf(t69_enumset1, axiom,
% 0.99/1.20    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.99/1.20  thf('32', plain,
% 0.99/1.20      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.99/1.20      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.99/1.20  thf(d2_tarski, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.99/1.20       ( ![D:$i]:
% 0.99/1.20         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.99/1.20  thf('33', plain,
% 0.99/1.20      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.99/1.20         (((X15) != (X14))
% 0.99/1.20          | (r2_hidden @ X15 @ X16)
% 0.99/1.20          | ((X16) != (k2_tarski @ X17 @ X14)))),
% 0.99/1.20      inference('cnf', [status(esa)], [d2_tarski])).
% 0.99/1.20  thf('34', plain,
% 0.99/1.20      (![X14 : $i, X17 : $i]: (r2_hidden @ X14 @ (k2_tarski @ X17 @ X14))),
% 0.99/1.20      inference('simplify', [status(thm)], ['33'])).
% 0.99/1.20  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.99/1.20      inference('sup+', [status(thm)], ['32', '34'])).
% 0.99/1.20  thf(t8_setfam_1, axiom,
% 0.99/1.20    (![A:$i,B:$i,C:$i]:
% 0.99/1.20     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.99/1.20       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.99/1.20  thf('36', plain,
% 0.99/1.20      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.99/1.20         (~ (r2_hidden @ X35 @ X36)
% 0.99/1.20          | ~ (r1_tarski @ X35 @ X37)
% 0.99/1.20          | (r1_tarski @ (k1_setfam_1 @ X36) @ X37))),
% 0.99/1.20      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.99/1.20  thf('37', plain,
% 0.99/1.20      (![X0 : $i, X1 : $i]:
% 0.99/1.20         ((r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X1)
% 0.99/1.20          | ~ (r1_tarski @ X0 @ X1))),
% 0.99/1.20      inference('sup-', [status(thm)], ['35', '36'])).
% 0.99/1.20  thf('38', plain,
% 0.99/1.20      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.99/1.20      inference('sup-', [status(thm)], ['31', '37'])).
% 0.99/1.20  thf('39', plain,
% 0.99/1.20      (![X10 : $i, X12 : $i]:
% 0.99/1.20         (((X10) = (X12))
% 0.99/1.20          | ~ (r1_tarski @ X12 @ X10)
% 0.99/1.20          | ~ (r1_tarski @ X10 @ X12))),
% 0.99/1.20      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.99/1.20  thf('40', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.99/1.20          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['38', '39'])).
% 0.99/1.20  thf('41', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (((X0) = (sk_C_1 @ X0 @ (k1_tarski @ X0)))
% 0.99/1.20          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['29', '40'])).
% 0.99/1.20  thf('42', plain,
% 0.99/1.20      (![X33 : $i, X34 : $i]:
% 0.99/1.20         (((X33) = (k1_xboole_0))
% 0.99/1.20          | ~ (r1_tarski @ X34 @ (sk_C_1 @ X34 @ X33))
% 0.99/1.20          | (r1_tarski @ X34 @ (k1_setfam_1 @ X33)))),
% 0.99/1.20      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.99/1.20  thf('43', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (r1_tarski @ X0 @ X0)
% 0.99/1.20          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.99/1.20          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.99/1.20          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.99/1.20      inference('sup-', [status(thm)], ['41', '42'])).
% 0.99/1.20  thf('44', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.99/1.20      inference('simplify', [status(thm)], ['30'])).
% 0.99/1.20  thf('45', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.99/1.20          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.99/1.20          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.99/1.20      inference('demod', [status(thm)], ['43', '44'])).
% 0.99/1.20  thf('46', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.99/1.20          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.99/1.20      inference('sup-', [status(thm)], ['38', '39'])).
% 0.99/1.20  thf('47', plain,
% 0.99/1.20      (![X0 : $i]:
% 0.99/1.20         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.99/1.20          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.99/1.20      inference('clc', [status(thm)], ['45', '46'])).
% 0.99/1.20  thf('48', plain, (![X26 : $i]: ((k1_xboole_0) != (k1_tarski @ X26))),
% 0.99/1.20      inference('demod', [status(thm)], ['8', '27'])).
% 0.99/1.20  thf('49', plain, (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))),
% 0.99/1.20      inference('clc', [status(thm)], ['47', '48'])).
% 0.99/1.20  thf('50', plain, (((sk_A) != (sk_A))),
% 0.99/1.20      inference('demod', [status(thm)], ['0', '49'])).
% 0.99/1.20  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.99/1.20  
% 0.99/1.20  % SZS output end Refutation
% 0.99/1.20  
% 0.99/1.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
