%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WsFzPk5V8D

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:43 EST 2020

% Result     : Theorem 0.72s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 251 expanded)
%              Number of leaves         :   16 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  436 (1943 expanded)
%              Number of equality atoms :   49 ( 199 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X31 @ X30 ) @ X30 )
      | ( r1_tarski @ X31 @ ( k1_setfam_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ ( k1_tarski @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t8_setfam_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ) )).

thf('9',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ X33 )
      | ~ ( r1_tarski @ X32 @ X34 )
      | ( r1_tarski @ ( k1_setfam_1 @ X33 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[t8_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','13'])).

thf('15',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ ( sk_C_2 @ X31 @ X30 ) )
      | ( r1_tarski @ X31 @ ( k1_setfam_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('22',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_A != sk_A )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ ( k1_tarski @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('28',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ ( k1_tarski @ X29 ) )
      | ( X28 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('29',plain,(
    ! [X29: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X29 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ k1_xboole_0 )
       != sk_A )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X1 )
      | ( ( sk_C @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['26','38'])).

thf('40',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('41',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['23'])).

thf('44',plain,(
    ( k1_setfam_1 @ k1_xboole_0 )
 != sk_A ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ( k1_setfam_1 @ k1_xboole_0 )
 != sk_A ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WsFzPk5V8D
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.72/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.72/0.90  % Solved by: fo/fo7.sh
% 0.72/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.72/0.90  % done 420 iterations in 0.411s
% 0.72/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.72/0.90  % SZS output start Refutation
% 0.72/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.72/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.72/0.90  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.72/0.90  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.72/0.90  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.72/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.72/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.72/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.72/0.90  thf(t6_setfam_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.72/0.90       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.72/0.90  thf('0', plain,
% 0.72/0.90      (![X30 : $i, X31 : $i]:
% 0.72/0.90         (((X30) = (k1_xboole_0))
% 0.72/0.90          | (r2_hidden @ (sk_C_2 @ X31 @ X30) @ X30)
% 0.72/0.90          | (r1_tarski @ X31 @ (k1_setfam_1 @ X30)))),
% 0.72/0.90      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.72/0.90  thf(d1_tarski, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.72/0.90       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.72/0.90  thf('1', plain,
% 0.72/0.90      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.72/0.90         (~ (r2_hidden @ X10 @ X9)
% 0.72/0.90          | ((X10) = (X7))
% 0.72/0.90          | ((X9) != (k1_tarski @ X7)))),
% 0.72/0.90      inference('cnf', [status(esa)], [d1_tarski])).
% 0.72/0.90  thf('2', plain,
% 0.72/0.90      (![X7 : $i, X10 : $i]:
% 0.72/0.90         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['1'])).
% 0.72/0.90  thf('3', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.72/0.90          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.72/0.90          | ((sk_C_2 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['0', '2'])).
% 0.72/0.90  thf(d10_xboole_0, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.72/0.90  thf('4', plain,
% 0.72/0.90      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.72/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.72/0.90  thf('5', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.72/0.90      inference('simplify', [status(thm)], ['4'])).
% 0.72/0.90  thf('6', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.72/0.90      inference('simplify', [status(thm)], ['4'])).
% 0.72/0.90  thf(l1_zfmisc_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.72/0.90  thf('7', plain,
% 0.72/0.90      (![X24 : $i, X25 : $i]:
% 0.72/0.90         ((r2_hidden @ X24 @ X25) | ~ (r1_tarski @ (k1_tarski @ X24) @ X25))),
% 0.72/0.90      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.72/0.90  thf('8', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['6', '7'])).
% 0.72/0.90  thf(t8_setfam_1, axiom,
% 0.72/0.90    (![A:$i,B:$i,C:$i]:
% 0.72/0.90     ( ( ( r2_hidden @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.72/0.90       ( r1_tarski @ ( k1_setfam_1 @ B ) @ C ) ))).
% 0.72/0.90  thf('9', plain,
% 0.72/0.90      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.72/0.90         (~ (r2_hidden @ X32 @ X33)
% 0.72/0.90          | ~ (r1_tarski @ X32 @ X34)
% 0.72/0.90          | (r1_tarski @ (k1_setfam_1 @ X33) @ X34))),
% 0.72/0.90      inference('cnf', [status(esa)], [t8_setfam_1])).
% 0.72/0.90  thf('10', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X1)
% 0.72/0.90          | ~ (r1_tarski @ X0 @ X1))),
% 0.72/0.90      inference('sup-', [status(thm)], ['8', '9'])).
% 0.72/0.90  thf('11', plain,
% 0.72/0.90      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.72/0.90      inference('sup-', [status(thm)], ['5', '10'])).
% 0.72/0.90  thf('12', plain,
% 0.72/0.90      (![X4 : $i, X6 : $i]:
% 0.72/0.90         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.72/0.90      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.72/0.90  thf('13', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.72/0.90          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['11', '12'])).
% 0.72/0.90  thf('14', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((sk_C_2 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.72/0.90          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.72/0.90          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['3', '13'])).
% 0.72/0.90  thf('15', plain,
% 0.72/0.90      (![X30 : $i, X31 : $i]:
% 0.72/0.90         (((X30) = (k1_xboole_0))
% 0.72/0.90          | ~ (r1_tarski @ X31 @ (sk_C_2 @ X31 @ X30))
% 0.72/0.90          | (r1_tarski @ X31 @ (k1_setfam_1 @ X30)))),
% 0.72/0.90      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.72/0.90  thf('16', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (r1_tarski @ X0 @ X0)
% 0.72/0.90          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.72/0.90          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.72/0.90          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.72/0.90          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['14', '15'])).
% 0.72/0.90  thf('17', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.72/0.90      inference('simplify', [status(thm)], ['4'])).
% 0.72/0.90  thf('18', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.72/0.90          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.72/0.90          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.72/0.90          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.72/0.90      inference('demod', [status(thm)], ['16', '17'])).
% 0.72/0.90  thf('19', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         ((r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.72/0.90          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.72/0.90          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.72/0.90      inference('simplify', [status(thm)], ['18'])).
% 0.72/0.90  thf('20', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.72/0.90          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.72/0.90      inference('sup-', [status(thm)], ['11', '12'])).
% 0.72/0.90  thf('21', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.72/0.90          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.72/0.90      inference('clc', [status(thm)], ['19', '20'])).
% 0.72/0.90  thf(t11_setfam_1, conjecture,
% 0.72/0.90    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.72/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.72/0.90    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.72/0.90    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.72/0.90  thf('22', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('23', plain,
% 0.72/0.90      ((((sk_A) != (sk_A)) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['21', '22'])).
% 0.72/0.90  thf('24', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['23'])).
% 0.72/0.90  thf('25', plain,
% 0.72/0.90      (![X24 : $i, X25 : $i]:
% 0.72/0.90         ((r2_hidden @ X24 @ X25) | ~ (r1_tarski @ (k1_tarski @ X24) @ X25))),
% 0.72/0.90      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.72/0.90  thf('26', plain,
% 0.72/0.90      (![X0 : $i]: (~ (r1_tarski @ k1_xboole_0 @ X0) | (r2_hidden @ sk_A @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['24', '25'])).
% 0.72/0.90  thf(d3_tarski, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( r1_tarski @ A @ B ) <=>
% 0.72/0.90       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.72/0.90  thf('27', plain,
% 0.72/0.90      (![X1 : $i, X3 : $i]:
% 0.72/0.90         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.72/0.90      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.90  thf(l3_zfmisc_1, axiom,
% 0.72/0.90    (![A:$i,B:$i]:
% 0.72/0.90     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.72/0.90       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.72/0.90  thf('28', plain,
% 0.72/0.90      (![X28 : $i, X29 : $i]:
% 0.72/0.90         ((r1_tarski @ X28 @ (k1_tarski @ X29)) | ((X28) != (k1_xboole_0)))),
% 0.72/0.90      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.72/0.90  thf('29', plain,
% 0.72/0.90      (![X29 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X29))),
% 0.72/0.90      inference('simplify', [status(thm)], ['28'])).
% 0.72/0.90  thf('30', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.90         (~ (r2_hidden @ X0 @ X1)
% 0.72/0.90          | (r2_hidden @ X0 @ X2)
% 0.72/0.90          | ~ (r1_tarski @ X1 @ X2))),
% 0.72/0.90      inference('cnf', [status(esa)], [d3_tarski])).
% 0.72/0.90  thf('31', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.72/0.90          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['29', '30'])).
% 0.72/0.90  thf('32', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((r1_tarski @ k1_xboole_0 @ X0)
% 0.72/0.90          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ (k1_tarski @ X1)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['27', '31'])).
% 0.72/0.90  thf('33', plain,
% 0.72/0.90      (![X7 : $i, X10 : $i]:
% 0.72/0.90         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['1'])).
% 0.72/0.90  thf('34', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['32', '33'])).
% 0.72/0.90  thf('35', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('36', plain,
% 0.72/0.90      (![X0 : $i]:
% 0.72/0.90         (((sk_C @ X0 @ k1_xboole_0) != (sk_A))
% 0.72/0.90          | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['34', '35'])).
% 0.72/0.90  thf('37', plain,
% 0.72/0.90      (![X0 : $i, X1 : $i]:
% 0.72/0.90         ((r1_tarski @ k1_xboole_0 @ X1) | ((sk_C @ X1 @ k1_xboole_0) = (X0)))),
% 0.72/0.90      inference('sup-', [status(thm)], ['32', '33'])).
% 0.72/0.90  thf('38', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.72/0.90      inference('clc', [status(thm)], ['36', '37'])).
% 0.72/0.90  thf('39', plain, (![X0 : $i]: (r2_hidden @ sk_A @ X0)),
% 0.72/0.90      inference('demod', [status(thm)], ['26', '38'])).
% 0.72/0.90  thf('40', plain,
% 0.72/0.90      (![X7 : $i, X10 : $i]:
% 0.72/0.90         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.72/0.90      inference('simplify', [status(thm)], ['1'])).
% 0.72/0.90  thf('41', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['39', '40'])).
% 0.72/0.90  thf('42', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.72/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.90  thf('43', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.72/0.90      inference('simplify', [status(thm)], ['23'])).
% 0.72/0.90  thf('44', plain, (((k1_setfam_1 @ k1_xboole_0) != (sk_A))),
% 0.72/0.90      inference('demod', [status(thm)], ['42', '43'])).
% 0.72/0.90  thf('45', plain, (((k1_setfam_1 @ k1_xboole_0) != (sk_A))),
% 0.72/0.90      inference('sup-', [status(thm)], ['41', '44'])).
% 0.72/0.90  thf('46', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.72/0.90      inference('sup-', [status(thm)], ['39', '40'])).
% 0.72/0.90  thf('47', plain, ($false),
% 0.72/0.90      inference('simplify_reflect+', [status(thm)], ['45', '46'])).
% 0.72/0.90  
% 0.72/0.90  % SZS output end Refutation
% 0.72/0.90  
% 0.72/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
