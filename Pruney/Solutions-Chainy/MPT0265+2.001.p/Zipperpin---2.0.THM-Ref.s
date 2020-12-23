%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QZU3p2M204

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:43 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 123 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  416 (1176 expanded)
%              Number of equality atoms :   57 ( 157 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t60_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( ( r2_hidden @ C @ B )
          & ( A != C ) )
        | ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
          = ( k1_tarski @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( ( r2_hidden @ C @ B )
            & ( A != C ) )
          | ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B )
            = ( k1_tarski @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( sk_A = sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
   <= ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
   <= ( sk_A = sk_C ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_xboole_0 @ X8 @ ( k1_tarski @ X7 ) )
        = ( k1_tarski @ X7 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('6',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) )
      = ( k1_tarski @ sk_C ) )
   <= ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('8',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_C @ sk_C ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_A = sk_C )
   <= ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('11',plain,
    ( ( ( k3_xboole_0 @ ( k2_tarski @ sk_C @ sk_C ) @ sk_B )
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A = sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('12',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_C ) )
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A = sk_C ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    sk_A != sk_C ),
    inference('simplify_reflect-',[status(thm)],['6','14'])).

thf('16',plain,
    ( ~ ( r2_hidden @ sk_C @ sk_B )
    | ( sk_A = sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('19',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k1_tarski @ A ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ( ( r2_hidden @ B @ C )
          | ( A = B ) ) ) ) )).

thf('21',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X9 @ X11 ) @ X12 )
        = ( k1_tarski @ X9 ) )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l38_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ sk_B )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X2 @ X3 ) )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ ( k1_tarski @ X0 ) )
        = ( k3_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ sk_B ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X0 @ sk_A ) @ ( k1_tarski @ X0 ) )
        = ( k3_xboole_0 @ sk_B @ ( k2_tarski @ X0 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t23_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) ) ) )).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X13 @ X14 ) @ ( k1_tarski @ X14 ) )
        = ( k1_tarski @ X13 ) )
      | ( X13 = X14 ) ) ),
    inference(cnf,[status(esa)],[t23_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ ( k2_tarski @ X0 @ sk_A ) )
        = ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_B )
      | ( sk_A = X0 ) ) ),
    inference('sup+',[status(thm)],['26','29'])).

thf('31',plain,(
    ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_C ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,(
    ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_A @ sk_C ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('35',plain,(
    ( k3_xboole_0 @ sk_B @ ( k2_tarski @ sk_C @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( sk_A = sk_C )
    | ( r2_hidden @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['30','35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_C @ sk_B )
    | ( sk_A = sk_C ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','17'])).

thf('39',plain,(
    sk_A = sk_C ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['19','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['18','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QZU3p2M204
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:11:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.73  % Solved by: fo/fo7.sh
% 0.51/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.73  % done 197 iterations in 0.274s
% 0.51/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.73  % SZS output start Refutation
% 0.51/0.73  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.51/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.73  thf(t60_zfmisc_1, conjecture,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( r2_hidden @ A @ B ) =>
% 0.51/0.73       ( ( ( r2_hidden @ C @ B ) & ( ( A ) != ( C ) ) ) | 
% 0.51/0.73         ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k1_tarski @ A ) ) ) ))).
% 0.51/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.73    (~( ![A:$i,B:$i,C:$i]:
% 0.51/0.73        ( ( r2_hidden @ A @ B ) =>
% 0.51/0.73          ( ( ( r2_hidden @ C @ B ) & ( ( A ) != ( C ) ) ) | 
% 0.51/0.73            ( ( k3_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) = ( k1_tarski @ A ) ) ) ) )),
% 0.51/0.73    inference('cnf.neg', [status(esa)], [t60_zfmisc_1])).
% 0.51/0.73  thf('0', plain, ((~ (r2_hidden @ sk_C @ sk_B) | ((sk_A) = (sk_C)))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('1', plain,
% 0.51/0.73      ((~ (r2_hidden @ sk_C @ sk_B)) <= (~ ((r2_hidden @ sk_C @ sk_B)))),
% 0.51/0.73      inference('split', [status(esa)], ['0'])).
% 0.51/0.73  thf('2', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.51/0.73      inference('split', [status(esa)], ['0'])).
% 0.51/0.73  thf('3', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('4', plain, (((r2_hidden @ sk_C @ sk_B)) <= ((((sk_A) = (sk_C))))),
% 0.51/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.51/0.73  thf(l31_zfmisc_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( r2_hidden @ A @ B ) =>
% 0.51/0.73       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.51/0.73  thf('5', plain,
% 0.51/0.73      (![X7 : $i, X8 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ X8 @ (k1_tarski @ X7)) = (k1_tarski @ X7))
% 0.51/0.73          | ~ (r2_hidden @ X7 @ X8))),
% 0.51/0.73      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.51/0.73  thf('6', plain,
% 0.51/0.73      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C)) = (k1_tarski @ sk_C)))
% 0.51/0.73         <= ((((sk_A) = (sk_C))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.73  thf('7', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.51/0.73      inference('split', [status(esa)], ['0'])).
% 0.51/0.73  thf('8', plain,
% 0.51/0.73      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (k1_tarski @ sk_A))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('9', plain,
% 0.51/0.73      ((((k3_xboole_0 @ (k2_tarski @ sk_C @ sk_C) @ sk_B) != (k1_tarski @ sk_A)))
% 0.51/0.73         <= ((((sk_A) = (sk_C))))),
% 0.51/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.73  thf('10', plain, ((((sk_A) = (sk_C))) <= ((((sk_A) = (sk_C))))),
% 0.51/0.73      inference('split', [status(esa)], ['0'])).
% 0.51/0.73  thf('11', plain,
% 0.51/0.73      ((((k3_xboole_0 @ (k2_tarski @ sk_C @ sk_C) @ sk_B) != (k1_tarski @ sk_C)))
% 0.51/0.73         <= ((((sk_A) = (sk_C))))),
% 0.51/0.73      inference('demod', [status(thm)], ['9', '10'])).
% 0.51/0.73  thf(t69_enumset1, axiom,
% 0.51/0.73    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.51/0.73  thf('12', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.51/0.73      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.51/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.51/0.73  thf('13', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.73  thf('14', plain,
% 0.51/0.73      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_C)) != (k1_tarski @ sk_C)))
% 0.51/0.73         <= ((((sk_A) = (sk_C))))),
% 0.51/0.73      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.51/0.73  thf('15', plain, (~ (((sk_A) = (sk_C)))),
% 0.51/0.73      inference('simplify_reflect-', [status(thm)], ['6', '14'])).
% 0.51/0.73  thf('16', plain, (~ ((r2_hidden @ sk_C @ sk_B)) | (((sk_A) = (sk_C)))),
% 0.51/0.73      inference('split', [status(esa)], ['0'])).
% 0.51/0.73  thf('17', plain, (~ ((r2_hidden @ sk_C @ sk_B))),
% 0.51/0.73      inference('sat_resolution*', [status(thm)], ['15', '16'])).
% 0.51/0.73  thf('18', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 0.51/0.73      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.51/0.73  thf('19', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('20', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf(l38_zfmisc_1, axiom,
% 0.51/0.73    (![A:$i,B:$i,C:$i]:
% 0.51/0.73     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) <=>
% 0.51/0.73       ( ( ~( r2_hidden @ A @ C ) ) & 
% 0.51/0.73         ( ( r2_hidden @ B @ C ) | ( ( A ) = ( B ) ) ) ) ))).
% 0.51/0.73  thf('21', plain,
% 0.51/0.73      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.51/0.73         (((k4_xboole_0 @ (k2_tarski @ X9 @ X11) @ X12) = (k1_tarski @ X9))
% 0.51/0.73          | ~ (r2_hidden @ X11 @ X12)
% 0.51/0.73          | (r2_hidden @ X9 @ X12))),
% 0.51/0.73      inference('cnf', [status(esa)], [l38_zfmisc_1])).
% 0.51/0.73  thf('22', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         ((r2_hidden @ X0 @ sk_B)
% 0.51/0.73          | ((k4_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ sk_B) = (k1_tarski @ X0)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.73  thf(t48_xboole_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.51/0.73  thf('23', plain,
% 0.51/0.73      (![X2 : $i, X3 : $i]:
% 0.51/0.73         ((k4_xboole_0 @ X2 @ (k4_xboole_0 @ X2 @ X3))
% 0.51/0.73           = (k3_xboole_0 @ X2 @ X3))),
% 0.51/0.73      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.51/0.73  thf('24', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (((k4_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ (k1_tarski @ X0))
% 0.51/0.73            = (k3_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ sk_B))
% 0.51/0.73          | (r2_hidden @ X0 @ sk_B))),
% 0.51/0.73      inference('sup+', [status(thm)], ['22', '23'])).
% 0.51/0.73  thf('25', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.73  thf('26', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (((k4_xboole_0 @ (k2_tarski @ X0 @ sk_A) @ (k1_tarski @ X0))
% 0.51/0.73            = (k3_xboole_0 @ sk_B @ (k2_tarski @ X0 @ sk_A)))
% 0.51/0.73          | (r2_hidden @ X0 @ sk_B))),
% 0.51/0.73      inference('demod', [status(thm)], ['24', '25'])).
% 0.51/0.73  thf(commutativity_k2_tarski, axiom,
% 0.51/0.73    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.51/0.73  thf('27', plain,
% 0.51/0.73      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.51/0.73  thf(t23_zfmisc_1, axiom,
% 0.51/0.73    (![A:$i,B:$i]:
% 0.51/0.73     ( ( ( A ) != ( B ) ) =>
% 0.51/0.73       ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) ) =
% 0.51/0.73         ( k1_tarski @ A ) ) ))).
% 0.51/0.73  thf('28', plain,
% 0.51/0.73      (![X13 : $i, X14 : $i]:
% 0.51/0.73         (((k4_xboole_0 @ (k2_tarski @ X13 @ X14) @ (k1_tarski @ X14))
% 0.51/0.73            = (k1_tarski @ X13))
% 0.51/0.73          | ((X13) = (X14)))),
% 0.51/0.73      inference('cnf', [status(esa)], [t23_zfmisc_1])).
% 0.51/0.73  thf('29', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]:
% 0.51/0.73         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.51/0.73            = (k1_tarski @ X0))
% 0.51/0.73          | ((X0) = (X1)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['27', '28'])).
% 0.51/0.73  thf('30', plain,
% 0.51/0.73      (![X0 : $i]:
% 0.51/0.73         (((k3_xboole_0 @ sk_B @ (k2_tarski @ X0 @ sk_A)) = (k1_tarski @ sk_A))
% 0.51/0.73          | (r2_hidden @ X0 @ sk_B)
% 0.51/0.73          | ((sk_A) = (X0)))),
% 0.51/0.73      inference('sup+', [status(thm)], ['26', '29'])).
% 0.51/0.73  thf('31', plain,
% 0.51/0.73      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_C) @ sk_B) != (k1_tarski @ sk_A))),
% 0.51/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.73  thf('32', plain,
% 0.51/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.73  thf('33', plain,
% 0.51/0.73      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_A @ sk_C)) != (k1_tarski @ sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['31', '32'])).
% 0.51/0.73  thf('34', plain,
% 0.51/0.73      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.51/0.73      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.51/0.73  thf('35', plain,
% 0.51/0.73      (((k3_xboole_0 @ sk_B @ (k2_tarski @ sk_C @ sk_A)) != (k1_tarski @ sk_A))),
% 0.51/0.73      inference('demod', [status(thm)], ['33', '34'])).
% 0.51/0.73  thf('36', plain,
% 0.51/0.73      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.51/0.73        | ((sk_A) = (sk_C))
% 0.51/0.73        | (r2_hidden @ sk_C @ sk_B))),
% 0.51/0.73      inference('sup-', [status(thm)], ['30', '35'])).
% 0.51/0.73  thf('37', plain, (((r2_hidden @ sk_C @ sk_B) | ((sk_A) = (sk_C)))),
% 0.51/0.73      inference('simplify', [status(thm)], ['36'])).
% 0.51/0.73  thf('38', plain, (~ (r2_hidden @ sk_C @ sk_B)),
% 0.51/0.73      inference('simpl_trail', [status(thm)], ['1', '17'])).
% 0.51/0.73  thf('39', plain, (((sk_A) = (sk_C))),
% 0.51/0.73      inference('clc', [status(thm)], ['37', '38'])).
% 0.51/0.73  thf('40', plain, ((r2_hidden @ sk_C @ sk_B)),
% 0.51/0.73      inference('demod', [status(thm)], ['19', '39'])).
% 0.51/0.73  thf('41', plain, ($false), inference('demod', [status(thm)], ['18', '40'])).
% 0.51/0.73  
% 0.51/0.73  % SZS output end Refutation
% 0.51/0.73  
% 0.51/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
