%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XXMHzwSrZk

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:16 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   62 (  81 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  385 ( 609 expanded)
%              Number of equality atoms :   43 (  69 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf('0',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X36 ) @ X35 )
        = X35 )
      | ~ ( r2_hidden @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','19'])).

thf('21',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['7','20'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_tarski @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X8 @ X9 ) @ X10 )
      = ( k3_xboole_0 @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X11 @ X12 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_C_1 ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('35',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_C_1 )
    = ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('37',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','26','37'])).

thf('39',plain,
    ( ( k1_tarski @ sk_D )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','38'])).

thf('40',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('42',plain,(
    ( k3_xboole_0 @ sk_C_1 @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XXMHzwSrZk
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 741 iterations in 0.284s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.73  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.54/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.73  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.54/0.73  thf(sk_D_type, type, sk_D: $i).
% 0.54/0.73  thf(t148_zfmisc_1, conjecture,
% 0.54/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.73     ( ( ( r1_tarski @ A @ B ) & 
% 0.54/0.73         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.54/0.73         ( r2_hidden @ D @ A ) ) =>
% 0.54/0.73       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.54/0.73        ( ( ( r1_tarski @ A @ B ) & 
% 0.54/0.73            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.54/0.73            ( r2_hidden @ D @ A ) ) =>
% 0.54/0.73          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.54/0.73  thf('0', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(l22_zfmisc_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r2_hidden @ A @ B ) =>
% 0.54/0.73       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      (![X35 : $i, X36 : $i]:
% 0.54/0.73         (((k2_xboole_0 @ (k1_tarski @ X36) @ X35) = (X35))
% 0.54/0.73          | ~ (r2_hidden @ X36 @ X35))),
% 0.54/0.73      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 0.54/0.73  thf('2', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['0', '1'])).
% 0.54/0.73  thf(t21_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (X13))),
% 0.54/0.73      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.54/0.73  thf('4', plain,
% 0.54/0.73      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A) = (k1_tarski @ sk_D))),
% 0.54/0.73      inference('sup+', [status(thm)], ['2', '3'])).
% 0.54/0.73  thf(commutativity_k3_xboole_0, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.54/0.73      inference('demod', [status(thm)], ['4', '5'])).
% 0.54/0.73  thf('7', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.73  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(t12_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (![X6 : $i, X7 : $i]:
% 0.54/0.73         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.54/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.73  thf('11', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.54/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (X13))),
% 0.54/0.73      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.54/0.73  thf('13', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.54/0.73      inference('sup+', [status(thm)], ['11', '12'])).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.73  thf('15', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.54/0.73      inference('demod', [status(thm)], ['13', '14'])).
% 0.54/0.73  thf(t16_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.54/0.73       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.54/0.73  thf('16', plain,
% 0.54/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.54/0.73           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.54/0.73  thf(t17_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.54/0.73  thf('17', plain,
% 0.54/0.73      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 0.54/0.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.54/0.73          (k3_xboole_0 @ X2 @ X1))),
% 0.54/0.73      inference('sup+', [status(thm)], ['16', '17'])).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.54/0.73      inference('sup+', [status(thm)], ['15', '18'])).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.54/0.73      inference('sup+', [status(thm)], ['8', '19'])).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      ((r1_tarski @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ (k1_tarski @ sk_D))),
% 0.54/0.73      inference('sup+', [status(thm)], ['7', '20'])).
% 0.54/0.73  thf(t28_xboole_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      (![X18 : $i, X19 : $i]:
% 0.54/0.73         (((k3_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_tarski @ X18 @ X19))),
% 0.54/0.73      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.73  thf('23', plain,
% 0.54/0.73      (((k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ (k1_tarski @ sk_D))
% 0.54/0.73         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.54/0.73  thf('24', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ (k3_xboole_0 @ X8 @ X9) @ X10)
% 0.54/0.73           = (k3_xboole_0 @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.54/0.73           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.54/0.73      inference('sup+', [status(thm)], ['24', '25'])).
% 0.54/0.73  thf('27', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('28', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.73  thf('29', plain,
% 0.54/0.73      (![X11 : $i, X12 : $i]: (r1_tarski @ (k3_xboole_0 @ X11 @ X12) @ X11)),
% 0.54/0.73      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.54/0.73  thf('30', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.54/0.73      inference('sup+', [status(thm)], ['28', '29'])).
% 0.54/0.73  thf('31', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_C_1)),
% 0.54/0.73      inference('sup+', [status(thm)], ['27', '30'])).
% 0.54/0.73  thf('32', plain,
% 0.54/0.73      (![X6 : $i, X7 : $i]:
% 0.54/0.73         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.54/0.73      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.54/0.73  thf('33', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D) @ sk_C_1) = (sk_C_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['31', '32'])).
% 0.54/0.73  thf('34', plain,
% 0.54/0.73      (![X13 : $i, X14 : $i]:
% 0.54/0.73         ((k3_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14)) = (X13))),
% 0.54/0.73      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.54/0.73  thf('35', plain,
% 0.54/0.73      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_C_1) = (k1_tarski @ sk_D))),
% 0.54/0.73      inference('sup+', [status(thm)], ['33', '34'])).
% 0.54/0.73  thf('36', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.73  thf('37', plain,
% 0.54/0.73      (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D)) = (k1_tarski @ sk_D))),
% 0.54/0.73      inference('demod', [status(thm)], ['35', '36'])).
% 0.54/0.73  thf('38', plain,
% 0.54/0.73      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D))
% 0.54/0.73         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.54/0.73      inference('demod', [status(thm)], ['23', '26', '37'])).
% 0.54/0.73  thf('39', plain, (((k1_tarski @ sk_D) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.54/0.73      inference('sup+', [status(thm)], ['6', '38'])).
% 0.54/0.73  thf('40', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('41', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.54/0.73  thf('42', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) != (k1_tarski @ sk_D))),
% 0.54/0.73      inference('demod', [status(thm)], ['40', '41'])).
% 0.54/0.73  thf('43', plain, ($false),
% 0.54/0.73      inference('simplify_reflect-', [status(thm)], ['39', '42'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
