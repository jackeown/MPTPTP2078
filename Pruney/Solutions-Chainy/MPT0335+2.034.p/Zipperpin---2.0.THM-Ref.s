%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WEgMtvRK13

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:17 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 103 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :   15
%              Number of atoms          :  481 ( 777 expanded)
%              Number of equality atoms :   51 (  85 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23
        = ( k1_tarski @ X22 ) )
      | ( X23 = k1_xboole_0 )
      | ~ ( r1_tarski @ X23 @ ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ X23 @ ( k1_tarski @ X24 ) )
      | ( X23 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('26',plain,(
    ! [X24: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X24 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('31',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('33',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) @ sk_B ) ),
    inference('sup+',[status(thm)],['35','40'])).

thf('42',plain,(
    r1_tarski @ k1_xboole_0 @ sk_B ),
    inference('sup+',[status(thm)],['28','41'])).

thf('43',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('44',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','24','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('47',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A ),
    inference(simplify,[status(thm)],['49'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('51',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('52',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X25 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( r2_hidden @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WEgMtvRK13
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.83  % Solved by: fo/fo7.sh
% 0.60/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.83  % done 859 iterations in 0.386s
% 0.60/0.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.83  % SZS output start Refutation
% 0.60/0.83  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.83  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.83  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.83  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.83  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.83  thf(t148_zfmisc_1, conjecture,
% 0.60/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.83     ( ( ( r1_tarski @ A @ B ) & 
% 0.60/0.83         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.60/0.83         ( r2_hidden @ D @ A ) ) =>
% 0.60/0.83       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.60/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.83        ( ( ( r1_tarski @ A @ B ) & 
% 0.60/0.83            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.60/0.83            ( r2_hidden @ D @ A ) ) =>
% 0.60/0.83          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.60/0.83    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.60/0.83  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(commutativity_k3_xboole_0, axiom,
% 0.60/0.83    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.60/0.83  thf('1', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.83  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf(t28_xboole_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.60/0.83  thf('3', plain,
% 0.60/0.83      (![X10 : $i, X11 : $i]:
% 0.60/0.83         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.60/0.83      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.83  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.60/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.83  thf('5', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.83  thf('6', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.60/0.83      inference('demod', [status(thm)], ['4', '5'])).
% 0.60/0.83  thf(t16_xboole_1, axiom,
% 0.60/0.83    (![A:$i,B:$i,C:$i]:
% 0.60/0.83     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.60/0.83       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.60/0.83  thf('7', plain,
% 0.60/0.83      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.83         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.60/0.83           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.60/0.83      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.60/0.83  thf(t17_xboole_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.60/0.83  thf('8', plain,
% 0.60/0.83      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.60/0.83      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.60/0.83  thf('9', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.83         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.60/0.83          (k3_xboole_0 @ X2 @ X1))),
% 0.60/0.83      inference('sup+', [status(thm)], ['7', '8'])).
% 0.60/0.83  thf('10', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.60/0.83      inference('sup+', [status(thm)], ['6', '9'])).
% 0.60/0.83  thf('11', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.60/0.83      inference('sup+', [status(thm)], ['1', '10'])).
% 0.60/0.83  thf('12', plain,
% 0.60/0.83      ((r1_tarski @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D))),
% 0.60/0.83      inference('sup+', [status(thm)], ['0', '11'])).
% 0.60/0.83  thf(l3_zfmisc_1, axiom,
% 0.60/0.83    (![A:$i,B:$i]:
% 0.60/0.83     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.60/0.83       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.60/0.83  thf('13', plain,
% 0.60/0.83      (![X22 : $i, X23 : $i]:
% 0.60/0.83         (((X23) = (k1_tarski @ X22))
% 0.60/0.83          | ((X23) = (k1_xboole_0))
% 0.60/0.83          | ~ (r1_tarski @ X23 @ (k1_tarski @ X22)))),
% 0.60/0.83      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.60/0.83  thf('14', plain,
% 0.60/0.83      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.60/0.83        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D)))),
% 0.60/0.83      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.83  thf('15', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('16', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.83  thf('17', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.60/0.83      inference('demod', [status(thm)], ['15', '16'])).
% 0.60/0.83  thf('18', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.60/0.83      inference('simplify_reflect-', [status(thm)], ['14', '17'])).
% 0.60/0.83  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.60/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.83  thf('20', plain,
% 0.60/0.83      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.83         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.60/0.83           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.60/0.83      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.60/0.83  thf('21', plain,
% 0.60/0.83      (![X0 : $i]:
% 0.60/0.83         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.60/0.83           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.60/0.83      inference('sup+', [status(thm)], ['19', '20'])).
% 0.60/0.83  thf('22', plain,
% 0.60/0.83      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A)
% 0.60/0.83         = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.60/0.83      inference('sup+', [status(thm)], ['18', '21'])).
% 0.60/0.83  thf('23', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.83  thf('24', plain,
% 0.60/0.83      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.83      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.83  thf('25', plain,
% 0.60/0.83      (![X23 : $i, X24 : $i]:
% 0.60/0.83         ((r1_tarski @ X23 @ (k1_tarski @ X24)) | ((X23) != (k1_xboole_0)))),
% 0.60/0.83      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.60/0.83  thf('26', plain,
% 0.60/0.83      (![X24 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X24))),
% 0.60/0.84      inference('simplify', [status(thm)], ['25'])).
% 0.60/0.84  thf('27', plain,
% 0.60/0.84      (![X10 : $i, X11 : $i]:
% 0.60/0.84         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.60/0.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.84  thf('28', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['26', '27'])).
% 0.60/0.84  thf('29', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('30', plain,
% 0.60/0.84      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.60/0.84      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.60/0.84  thf('31', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_B)),
% 0.60/0.84      inference('sup+', [status(thm)], ['29', '30'])).
% 0.60/0.84  thf('32', plain,
% 0.60/0.84      (![X10 : $i, X11 : $i]:
% 0.60/0.84         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.60/0.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.84  thf('33', plain,
% 0.60/0.84      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) = (k1_tarski @ sk_D))),
% 0.60/0.84      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.84  thf('34', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.84  thf('35', plain,
% 0.60/0.84      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.60/0.84      inference('demod', [status(thm)], ['33', '34'])).
% 0.60/0.84  thf('36', plain,
% 0.60/0.84      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.84         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.60/0.84           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.60/0.84      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.60/0.84  thf('37', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.84  thf('38', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X2 @ X1))
% 0.60/0.84           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.60/0.84      inference('sup+', [status(thm)], ['36', '37'])).
% 0.60/0.84  thf('39', plain,
% 0.60/0.84      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.60/0.84      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.60/0.84  thf('40', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1)),
% 0.60/0.84      inference('sup+', [status(thm)], ['38', '39'])).
% 0.60/0.84  thf('41', plain,
% 0.60/0.84      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_D)) @ sk_B)),
% 0.60/0.84      inference('sup+', [status(thm)], ['35', '40'])).
% 0.60/0.84  thf('42', plain, ((r1_tarski @ k1_xboole_0 @ sk_B)),
% 0.60/0.84      inference('sup+', [status(thm)], ['28', '41'])).
% 0.60/0.84  thf('43', plain,
% 0.60/0.84      (![X10 : $i, X11 : $i]:
% 0.60/0.84         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.60/0.84      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.84  thf('44', plain, (((k3_xboole_0 @ k1_xboole_0 @ sk_B) = (k1_xboole_0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['42', '43'])).
% 0.60/0.84  thf('45', plain,
% 0.60/0.84      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 0.60/0.84      inference('demod', [status(thm)], ['22', '23', '24', '44'])).
% 0.60/0.84  thf('46', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.60/0.84      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.84  thf(d7_xboole_0, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.60/0.84       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.84  thf('47', plain,
% 0.60/0.84      (![X2 : $i, X4 : $i]:
% 0.60/0.84         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.60/0.84      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.84  thf('48', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['46', '47'])).
% 0.60/0.84  thf('49', plain,
% 0.60/0.84      ((((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.84        | (r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['45', '48'])).
% 0.60/0.84  thf('50', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_A)),
% 0.60/0.84      inference('simplify', [status(thm)], ['49'])).
% 0.60/0.84  thf(t69_enumset1, axiom,
% 0.60/0.84    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.60/0.84  thf('51', plain,
% 0.60/0.84      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.60/0.84      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.84  thf(t55_zfmisc_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.60/0.84  thf('52', plain,
% 0.60/0.84      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.84         (~ (r1_xboole_0 @ (k2_tarski @ X25 @ X26) @ X27)
% 0.60/0.84          | ~ (r2_hidden @ X25 @ X27))),
% 0.60/0.84      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.60/0.84  thf('53', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.60/0.84      inference('sup-', [status(thm)], ['51', '52'])).
% 0.60/0.84  thf('54', plain, (~ (r2_hidden @ sk_D @ sk_A)),
% 0.60/0.84      inference('sup-', [status(thm)], ['50', '53'])).
% 0.60/0.84  thf('55', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('56', plain, ($false), inference('demod', [status(thm)], ['54', '55'])).
% 0.60/0.84  
% 0.60/0.84  % SZS output end Refutation
% 0.60/0.84  
% 0.60/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
