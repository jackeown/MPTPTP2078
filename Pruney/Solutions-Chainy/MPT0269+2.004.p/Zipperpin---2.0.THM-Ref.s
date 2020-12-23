%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AbtlKnLxUC

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 147 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :  507 (1070 expanded)
%              Number of equality atoms :   57 ( 147 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('2',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X16: $i] :
      ( ( k3_xboole_0 @ X16 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','14'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X39: $i,X40: $i] :
      ( ( ( k4_xboole_0 @ X39 @ ( k1_tarski @ X40 ) )
        = X39 )
      | ( r2_hidden @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('21',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','14'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X11: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X13 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['21','24'])).

thf('26',plain,
    ( ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['2','14'])).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('29',plain,
    ( ( ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != k1_xboole_0 )
    | ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X11 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['32'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A )
    | ( ( k1_tarski @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_A
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ~ ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['35','36'])).

thf('38',plain,(
    ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
 != k1_xboole_0 ),
    inference(clc,[status(thm)],['29','37'])).

thf('39',plain,(
    r2_hidden @ sk_B @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','38'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    r1_tarski @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference(simplify,[status(thm)],['32'])).

thf('42',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('45',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( X30 = X27 )
      | ( X29
       != ( k1_tarski @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('46',plain,(
    ! [X27: $i,X30: $i] :
      ( ( X30 = X27 )
      | ~ ( r2_hidden @ X30 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( ( sk_C @ X0 @ sk_A )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( r2_hidden @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['19','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AbtlKnLxUC
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:27:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 126 iterations in 0.049s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(t66_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.20/0.48          ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ~( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_xboole_0 ) ) & 
% 0.20/0.48             ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t66_zfmisc_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d6_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k5_xboole_0 @ A @ B ) =
% 0.20/0.48       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((k5_xboole_0 @ X6 @ X7)
% 0.20/0.48           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X7 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.48         = (k2_xboole_0 @ k1_xboole_0 @ 
% 0.20/0.48            (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['0', '1'])).
% 0.20/0.48  thf(t2_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (![X16 : $i]: ((k3_xboole_0 @ X16 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.48  thf(t100_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X14 : $i, X15 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X14 @ X15)
% 0.20/0.48           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf(t5_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.48  thf('6', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 0.20/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.48  thf('7', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]:
% 0.20/0.48         ((k5_xboole_0 @ X6 @ X7)
% 0.20/0.48           = (k2_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ (k4_xboole_0 @ X7 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((k5_xboole_0 @ X0 @ k1_xboole_0)
% 0.20/0.48           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf('10', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 0.20/0.48      inference('cnf', [status(esa)], [t5_boole])).
% 0.20/0.48  thf(t4_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X23 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X23) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.48  thf('12', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.48  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.48  thf('14', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.48         = (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '14'])).
% 0.20/0.48  thf(t38_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.20/0.48       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X19 : $i, X20 : $i]:
% 0.20/0.48         (((X19) = (k1_xboole_0))
% 0.20/0.48          | ~ (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X19)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      ((~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))
% 0.20/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf(t65_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.48       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X39 : $i, X40 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ X39 @ (k1_tarski @ X40)) = (X39))
% 0.20/0.48          | (r2_hidden @ X40 @ X39))),
% 0.20/0.48      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.48         = (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '14'])).
% 0.20/0.48  thf(t36_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.20/0.48      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.20/0.48  thf(l32_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X11 : $i, X13 : $i]:
% 0.20/0.48         (((k4_xboole_0 @ X11 @ X13) = (k1_xboole_0))
% 0.20/0.48          | ~ (r1_tarski @ X11 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((k4_xboole_0 @ (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) @ 
% 0.20/0.48         (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['21', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      ((((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))
% 0.20/0.48        | (r2_hidden @ sk_B @ (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.20/0.48      inference('sup+', [status(thm)], ['20', '25'])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B))
% 0.20/0.48         = (k4_xboole_0 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['2', '14'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         ((r1_tarski @ X11 @ X12)
% 0.20/0.48          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      ((((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (k1_xboole_0))
% 0.20/0.48        | (r1_tarski @ (k1_tarski @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain,
% 0.20/0.48      (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         ((r1_tarski @ X11 @ X12)
% 0.20/0.48          | ((k4_xboole_0 @ X11 @ X12) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | (r1_tarski @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.48  thf('33', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.48  thf(d10_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      (![X8 : $i, X10 : $i]:
% 0.20/0.48         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)
% 0.20/0.48        | ((k1_tarski @ sk_B) = (sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.48  thf('36', plain, (((sk_A) != (k1_tarski @ sk_B))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('37', plain, (~ (r1_tarski @ (k1_tarski @ sk_B) @ sk_A)),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['35', '36'])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (((k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (k1_xboole_0))),
% 0.20/0.48      inference('clc', [status(thm)], ['29', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((r2_hidden @ sk_B @ (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('simplify_reflect-', [status(thm)], ['26', '38'])).
% 0.20/0.48  thf(d3_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X3 : $i, X5 : $i]:
% 0.20/0.48         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('41', plain, ((r1_tarski @ sk_A @ (k1_tarski @ sk_B))),
% 0.20/0.48      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.48          | (r2_hidden @ X2 @ X4)
% 0.20/0.48          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r2_hidden @ X0 @ (k1_tarski @ sk_B)) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_tarski @ sk_A @ X0)
% 0.20/0.48          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['40', '43'])).
% 0.20/0.48  thf(d1_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.20/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X27 : $i, X29 : $i, X30 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X30 @ X29)
% 0.20/0.48          | ((X30) = (X27))
% 0.20/0.48          | ((X29) != (k1_tarski @ X27)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X27 : $i, X30 : $i]:
% 0.20/0.48         (((X30) = (X27)) | ~ (r2_hidden @ X30 @ (k1_tarski @ X27)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_C @ X0 @ sk_A) = (sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['44', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X3 : $i, X5 : $i]:
% 0.20/0.48         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (r2_hidden @ sk_B @ X0)
% 0.20/0.48          | (r1_tarski @ sk_A @ X0)
% 0.20/0.48          | (r1_tarski @ sk_A @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (r2_hidden @ sk_B @ X0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['49'])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_A @ (k1_tarski @ sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['39', '50'])).
% 0.20/0.48  thf('52', plain, ($false), inference('demod', [status(thm)], ['19', '51'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
