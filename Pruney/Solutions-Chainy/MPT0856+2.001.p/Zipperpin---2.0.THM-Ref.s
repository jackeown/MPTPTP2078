%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EpsQhYFkFq

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  75 expanded)
%              Number of leaves         :   23 (  30 expanded)
%              Depth                    :   10
%              Number of atoms          :  333 ( 530 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t12_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X38 ) @ X39 )
      | ~ ( r2_hidden @ X38 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('3',plain,(
    ! [X32: $i] :
      ( ( k1_ordinal1 @ X32 )
      = ( k2_xboole_0 @ X32 @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_ordinal1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_ordinal1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_ordinal1 @ sk_B ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ( X34 = X33 )
      | ( r2_hidden @ X34 @ X33 )
      | ~ ( r2_hidden @ X34 @ ( k1_ordinal1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('12',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X38 ) @ X40 )
      | ~ ( r2_hidden @ X38 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('17',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['13'])).

thf('19',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['13'])).

thf('21',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['19','20'])).

thf('22',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['14','21'])).

thf('23',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['12','22'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('24',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X30 ) @ X31 )
      | ( r2_hidden @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('25',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

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

thf('26',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    r2_hidden @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['23','28'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r1_tarski @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('31',plain,(
    ~ ( r1_tarski @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['31','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EpsQhYFkFq
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:23:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 190 iterations in 0.075s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.54  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.54  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.54  thf(t12_mcart_1, conjecture,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.21/0.54       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.54         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.54        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.21/0.54          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.21/0.54            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t12_mcart_1])).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_2))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(t10_mcart_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.21/0.54       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.21/0.54         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.21/0.54         ((r2_hidden @ (k1_mcart_1 @ X38) @ X39)
% 0.21/0.54          | ~ (r2_hidden @ X38 @ (k2_zfmisc_1 @ X39 @ X40)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.54  thf('2', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf(d1_ordinal1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      (![X32 : $i]:
% 0.21/0.54         ((k1_ordinal1 @ X32) = (k2_xboole_0 @ X32 @ (k1_tarski @ X32)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.21/0.54  thf(commutativity_k2_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.54      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.21/0.54  thf(t7_xboole_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      (![X0 : $i]: (r1_tarski @ (k1_tarski @ X0) @ (k1_ordinal1 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['3', '6'])).
% 0.21/0.54  thf(d3_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.54          | (r2_hidden @ X2 @ X4)
% 0.21/0.54          | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         ((r2_hidden @ X1 @ (k1_ordinal1 @ X0))
% 0.21/0.54          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.54  thf('10', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_ordinal1 @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['2', '9'])).
% 0.21/0.54  thf(t13_ordinal1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.21/0.54       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X33 : $i, X34 : $i]:
% 0.21/0.54         (((X34) = (X33))
% 0.21/0.54          | (r2_hidden @ X34 @ X33)
% 0.21/0.54          | ~ (r2_hidden @ X34 @ (k1_ordinal1 @ X33)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.21/0.54        | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 0.21/0.54        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.54         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.54      inference('split', [status(esa)], ['13'])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_2))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.21/0.54         ((r2_hidden @ (k2_mcart_1 @ X38) @ X40)
% 0.21/0.54          | ~ (r2_hidden @ X38 @ (k2_zfmisc_1 @ X39 @ X40)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.21/0.54  thf('17', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2)),
% 0.21/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('18', plain,
% 0.21/0.54      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))
% 0.21/0.54         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2)))),
% 0.21/0.54      inference('split', [status(esa)], ['13'])).
% 0.21/0.54  thf('19', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))),
% 0.21/0.54      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.21/0.54       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_2))),
% 0.21/0.54      inference('split', [status(esa)], ['13'])).
% 0.21/0.54  thf('21', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.21/0.54      inference('sat_resolution*', [status(thm)], ['19', '20'])).
% 0.21/0.54  thf('22', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.21/0.54      inference('simpl_trail', [status(thm)], ['14', '21'])).
% 0.21/0.54  thf('23', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['12', '22'])).
% 0.21/0.54  thf(l27_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      (![X30 : $i, X31 : $i]:
% 0.21/0.54         ((r1_xboole_0 @ (k1_tarski @ X30) @ X31) | (r2_hidden @ X30 @ X31))),
% 0.21/0.54      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.54  thf('25', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf(t3_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.54          | ~ (r2_hidden @ X8 @ X9)
% 0.21/0.54          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.21/0.54          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         ((r2_hidden @ sk_B @ X0) | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['24', '27'])).
% 0.21/0.54  thf('29', plain, ((r2_hidden @ sk_B @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['23', '28'])).
% 0.21/0.54  thf(t7_ordinal1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('30', plain,
% 0.21/0.54      (![X36 : $i, X37 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X36 @ X37) | ~ (r1_tarski @ X37 @ X36))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.21/0.54  thf('31', plain, (~ (r1_tarski @ sk_B @ sk_B)),
% 0.21/0.54      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('33', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.21/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.54  thf('34', plain, ($false), inference('demod', [status(thm)], ['31', '33'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
