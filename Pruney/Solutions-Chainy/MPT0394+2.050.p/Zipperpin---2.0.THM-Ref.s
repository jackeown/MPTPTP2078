%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.szJM7YJGCW

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:51 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 143 expanded)
%              Number of leaves         :   23 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  460 (1247 expanded)
%              Number of equality atoms :   47 ( 101 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( k2_enumset1 @ X16 @ X17 @ X18 @ X19 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X16 @ X17 @ X18 ) @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k2_enumset1 @ X28 @ X28 @ X29 @ X30 )
      = ( k1_enumset1 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('6',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X37: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X35 @ X36 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X35 ) @ ( k1_setfam_1 @ X36 ) ) )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X37: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(t16_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        & ( A = B ) ) )).

thf('18',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X34 ) )
      | ( X33 != X34 ) ) ),
    inference(cnf,[status(esa)],[t16_zfmisc_1])).

thf('19',plain,(
    ! [X34: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X7: $i] :
      ( ( r1_xboole_0 @ X7 @ X7 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('22',plain,(
    r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','36'])).

thf('38',plain,(
    ! [X34: $i] :
      ~ ( r1_xboole_0 @ ( k1_tarski @ X34 ) @ ( k1_tarski @ X34 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('39',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['20','36'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.szJM7YJGCW
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:52:40 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.61/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.61/0.80  % Solved by: fo/fo7.sh
% 0.61/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.80  % done 886 iterations in 0.346s
% 0.61/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.61/0.80  % SZS output start Refutation
% 0.61/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.61/0.80  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.61/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.80  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.61/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.61/0.80  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.61/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.61/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.61/0.80  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.61/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.61/0.80  thf(t70_enumset1, axiom,
% 0.61/0.80    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.61/0.80  thf('0', plain,
% 0.61/0.80      (![X26 : $i, X27 : $i]:
% 0.61/0.80         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.61/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.61/0.80  thf(t69_enumset1, axiom,
% 0.61/0.80    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.61/0.80  thf('1', plain, (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.61/0.80      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.61/0.80  thf('2', plain,
% 0.61/0.80      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['0', '1'])).
% 0.61/0.80  thf(t46_enumset1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.80     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.61/0.80       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.61/0.80  thf('3', plain,
% 0.61/0.80      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.61/0.80         ((k2_enumset1 @ X16 @ X17 @ X18 @ X19)
% 0.61/0.80           = (k2_xboole_0 @ (k1_enumset1 @ X16 @ X17 @ X18) @ (k1_tarski @ X19)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.61/0.80  thf('4', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.61/0.80           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['2', '3'])).
% 0.61/0.80  thf(t71_enumset1, axiom,
% 0.61/0.80    (![A:$i,B:$i,C:$i]:
% 0.61/0.80     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.61/0.80  thf('5', plain,
% 0.61/0.80      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.61/0.80         ((k2_enumset1 @ X28 @ X28 @ X29 @ X30)
% 0.61/0.80           = (k1_enumset1 @ X28 @ X29 @ X30))),
% 0.61/0.80      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.61/0.80  thf('6', plain,
% 0.61/0.80      (![X26 : $i, X27 : $i]:
% 0.61/0.80         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.61/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.61/0.80  thf('7', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['5', '6'])).
% 0.61/0.80  thf('8', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.61/0.80           = (k2_tarski @ X1 @ X0))),
% 0.61/0.80      inference('sup+', [status(thm)], ['4', '7'])).
% 0.61/0.80  thf(t11_setfam_1, axiom,
% 0.61/0.80    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.61/0.80  thf('9', plain, (![X37 : $i]: ((k1_setfam_1 @ (k1_tarski @ X37)) = (X37))),
% 0.61/0.80      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.61/0.80  thf(t10_setfam_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.61/0.80          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.61/0.80            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.61/0.80  thf('10', plain,
% 0.61/0.80      (![X35 : $i, X36 : $i]:
% 0.61/0.80         (((X35) = (k1_xboole_0))
% 0.61/0.80          | ((k1_setfam_1 @ (k2_xboole_0 @ X35 @ X36))
% 0.61/0.80              = (k3_xboole_0 @ (k1_setfam_1 @ X35) @ (k1_setfam_1 @ X36)))
% 0.61/0.80          | ((X36) = (k1_xboole_0)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.61/0.80  thf('11', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.61/0.80            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.61/0.80          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.61/0.80          | ((X1) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.61/0.80  thf('12', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.61/0.80            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.61/0.80          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.61/0.80          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup+', [status(thm)], ['8', '11'])).
% 0.61/0.80  thf('13', plain, (![X37 : $i]: ((k1_setfam_1 @ (k1_tarski @ X37)) = (X37))),
% 0.61/0.80      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.61/0.80  thf('14', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.61/0.80          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.61/0.80          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.61/0.80      inference('demod', [status(thm)], ['12', '13'])).
% 0.61/0.80  thf(t12_setfam_1, conjecture,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.61/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.80    (~( ![A:$i,B:$i]:
% 0.61/0.80        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.61/0.80    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.61/0.80  thf('15', plain,
% 0.61/0.80      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.61/0.80         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.61/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.80  thf('16', plain,
% 0.61/0.80      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.61/0.80        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.61/0.80        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['14', '15'])).
% 0.61/0.80  thf('17', plain,
% 0.61/0.80      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.61/0.80        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.61/0.80      inference('simplify', [status(thm)], ['16'])).
% 0.61/0.80  thf(t16_zfmisc_1, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) & 
% 0.61/0.80          ( ( A ) = ( B ) ) ) ))).
% 0.61/0.80  thf('18', plain,
% 0.61/0.80      (![X33 : $i, X34 : $i]:
% 0.61/0.80         (~ (r1_xboole_0 @ (k1_tarski @ X33) @ (k1_tarski @ X34))
% 0.61/0.80          | ((X33) != (X34)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t16_zfmisc_1])).
% 0.61/0.80  thf('19', plain,
% 0.61/0.80      (![X34 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X34))),
% 0.61/0.80      inference('simplify', [status(thm)], ['18'])).
% 0.61/0.80  thf('20', plain,
% 0.61/0.80      ((~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0)
% 0.61/0.80        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.61/0.80      inference('sup-', [status(thm)], ['17', '19'])).
% 0.61/0.80  thf(t66_xboole_1, axiom,
% 0.61/0.80    (![A:$i]:
% 0.61/0.80     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.61/0.80       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.61/0.80  thf('21', plain,
% 0.61/0.80      (![X7 : $i]: ((r1_xboole_0 @ X7 @ X7) | ((X7) != (k1_xboole_0)))),
% 0.61/0.80      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.61/0.80  thf('22', plain, ((r1_xboole_0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.61/0.80      inference('simplify', [status(thm)], ['21'])).
% 0.61/0.80  thf(t3_xboole_0, axiom,
% 0.61/0.80    (![A:$i,B:$i]:
% 0.61/0.80     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.61/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.61/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.61/0.80            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.61/0.80  thf('23', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.80  thf('24', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.80  thf('25', plain,
% 0.61/0.80      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X2 @ X0)
% 0.61/0.80          | ~ (r2_hidden @ X2 @ X3)
% 0.61/0.80          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.80  thf('26', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.61/0.80          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.61/0.80          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.61/0.80      inference('sup-', [status(thm)], ['24', '25'])).
% 0.61/0.80  thf('27', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.61/0.80          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.61/0.80          | (r1_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('sup-', [status(thm)], ['23', '26'])).
% 0.61/0.80  thf('28', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('simplify', [status(thm)], ['27'])).
% 0.61/0.80  thf('29', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['22', '28'])).
% 0.61/0.80  thf('30', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.80  thf('31', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.80  thf('32', plain,
% 0.61/0.80      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.61/0.80         (~ (r2_hidden @ X2 @ X0)
% 0.61/0.80          | ~ (r2_hidden @ X2 @ X3)
% 0.61/0.80          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.61/0.80      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.61/0.80  thf('33', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.80         ((r1_xboole_0 @ X1 @ X0)
% 0.61/0.80          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.61/0.80          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.61/0.80      inference('sup-', [status(thm)], ['31', '32'])).
% 0.61/0.80  thf('34', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         ((r1_xboole_0 @ X0 @ X1)
% 0.61/0.80          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.61/0.80          | (r1_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('sup-', [status(thm)], ['30', '33'])).
% 0.61/0.80  thf('35', plain,
% 0.61/0.80      (![X0 : $i, X1 : $i]:
% 0.61/0.80         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.61/0.80      inference('simplify', [status(thm)], ['34'])).
% 0.61/0.80  thf('36', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['29', '35'])).
% 0.61/0.80  thf('37', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.61/0.80      inference('demod', [status(thm)], ['20', '36'])).
% 0.61/0.80  thf('38', plain,
% 0.61/0.80      (![X34 : $i]: ~ (r1_xboole_0 @ (k1_tarski @ X34) @ (k1_tarski @ X34))),
% 0.61/0.80      inference('simplify', [status(thm)], ['18'])).
% 0.61/0.80  thf('39', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['37', '38'])).
% 0.61/0.80  thf('40', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.61/0.80      inference('demod', [status(thm)], ['20', '36'])).
% 0.61/0.80  thf('41', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.61/0.80      inference('sup-', [status(thm)], ['22', '28'])).
% 0.61/0.80  thf('42', plain, ($false),
% 0.61/0.80      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.61/0.80  
% 0.61/0.80  % SZS output end Refutation
% 0.61/0.80  
% 0.61/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
