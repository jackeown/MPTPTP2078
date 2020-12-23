%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1YMJStpC3n

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:16 EST 2020

% Result     : Theorem 1.13s
% Output     : Refutation 1.13s
% Verified   : 
% Statistics : Number of formulae       :   65 (  87 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :   15
%              Number of atoms          :  410 ( 660 expanded)
%              Number of equality atoms :   46 (  75 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
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

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ sk_C_1 ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_C_1 )
    = sk_C_1 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('15',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['17','18'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k3_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k3_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','25'])).

thf('27',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_C_1 ) @ ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['11','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('33',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X14 @ X15 ) @ X16 )
      = ( k3_xboole_0 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('35',plain,(
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l22_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('36',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X38 ) @ X37 )
        = X37 )
      | ~ ( r2_hidden @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[l22_zfmisc_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X20 @ ( k2_xboole_0 @ X20 @ X21 ) )
      = X20 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('39',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34','41'])).

thf('43',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['10','42'])).

thf('44',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ( k3_xboole_0 @ sk_C_1 @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1YMJStpC3n
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:52:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.13/1.35  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.13/1.35  % Solved by: fo/fo7.sh
% 1.13/1.35  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.13/1.35  % done 2020 iterations in 0.894s
% 1.13/1.35  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.13/1.35  % SZS output start Refutation
% 1.13/1.35  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.13/1.35  thf(sk_A_type, type, sk_A: $i).
% 1.13/1.35  thf(sk_B_type, type, sk_B: $i).
% 1.13/1.35  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.13/1.35  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.13/1.35  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.13/1.35  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.13/1.35  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.13/1.35  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.13/1.35  thf(t148_zfmisc_1, conjecture,
% 1.13/1.35    (![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.35     ( ( ( r1_tarski @ A @ B ) & 
% 1.13/1.35         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.13/1.35         ( r2_hidden @ D @ A ) ) =>
% 1.13/1.35       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 1.13/1.35  thf(zf_stmt_0, negated_conjecture,
% 1.13/1.35    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.13/1.35        ( ( ( r1_tarski @ A @ B ) & 
% 1.13/1.35            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 1.13/1.35            ( r2_hidden @ D @ A ) ) =>
% 1.13/1.35          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 1.13/1.35    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 1.13/1.35  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf(commutativity_k3_xboole_0, axiom,
% 1.13/1.35    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.13/1.35  thf('1', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.35  thf(t17_xboole_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.13/1.35  thf('2', plain,
% 1.13/1.35      (![X17 : $i, X18 : $i]: (r1_tarski @ (k3_xboole_0 @ X17 @ X18) @ X17)),
% 1.13/1.35      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.13/1.35  thf('3', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.13/1.35      inference('sup+', [status(thm)], ['1', '2'])).
% 1.13/1.35  thf('4', plain, ((r1_tarski @ (k1_tarski @ sk_D_1) @ sk_C_1)),
% 1.13/1.35      inference('sup+', [status(thm)], ['0', '3'])).
% 1.13/1.35  thf(t12_xboole_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.13/1.35  thf('5', plain,
% 1.13/1.35      (![X12 : $i, X13 : $i]:
% 1.13/1.35         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 1.13/1.35      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.13/1.35  thf('6', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_C_1) = (sk_C_1))),
% 1.13/1.35      inference('sup-', [status(thm)], ['4', '5'])).
% 1.13/1.35  thf(t21_xboole_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 1.13/1.35  thf('7', plain,
% 1.13/1.35      (![X20 : $i, X21 : $i]:
% 1.13/1.35         ((k3_xboole_0 @ X20 @ (k2_xboole_0 @ X20 @ X21)) = (X20))),
% 1.13/1.35      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.13/1.35  thf('8', plain,
% 1.13/1.35      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.13/1.35      inference('sup+', [status(thm)], ['6', '7'])).
% 1.13/1.35  thf('9', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.35  thf('10', plain,
% 1.13/1.35      (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D_1)) = (k1_tarski @ sk_D_1))),
% 1.13/1.35      inference('demod', [status(thm)], ['8', '9'])).
% 1.13/1.35  thf('11', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('12', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.35  thf('13', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('14', plain,
% 1.13/1.35      (![X12 : $i, X13 : $i]:
% 1.13/1.35         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 1.13/1.35      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.13/1.35  thf('15', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 1.13/1.35      inference('sup-', [status(thm)], ['13', '14'])).
% 1.13/1.35  thf('16', plain,
% 1.13/1.35      (![X20 : $i, X21 : $i]:
% 1.13/1.35         ((k3_xboole_0 @ X20 @ (k2_xboole_0 @ X20 @ X21)) = (X20))),
% 1.13/1.35      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.13/1.35  thf('17', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 1.13/1.35      inference('sup+', [status(thm)], ['15', '16'])).
% 1.13/1.35  thf('18', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.35  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 1.13/1.35      inference('demod', [status(thm)], ['17', '18'])).
% 1.13/1.35  thf(t16_xboole_1, axiom,
% 1.13/1.35    (![A:$i,B:$i,C:$i]:
% 1.13/1.35     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.13/1.35       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.13/1.35  thf('20', plain,
% 1.13/1.35      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.13/1.35         ((k3_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16)
% 1.13/1.35           = (k3_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.13/1.35  thf('21', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((k3_xboole_0 @ sk_A @ X0)
% 1.13/1.35           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 1.13/1.35      inference('sup+', [status(thm)], ['19', '20'])).
% 1.13/1.35  thf('22', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         ((k3_xboole_0 @ sk_A @ X0)
% 1.13/1.35           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)))),
% 1.13/1.35      inference('sup+', [status(thm)], ['12', '21'])).
% 1.13/1.35  thf('23', plain,
% 1.13/1.35      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.13/1.35         ((k3_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16)
% 1.13/1.35           = (k3_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.13/1.35  thf('24', plain,
% 1.13/1.35      (![X17 : $i, X18 : $i]: (r1_tarski @ (k3_xboole_0 @ X17 @ X18) @ X17)),
% 1.13/1.35      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.13/1.35  thf('25', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.13/1.35         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.13/1.35          (k3_xboole_0 @ X2 @ X1))),
% 1.13/1.35      inference('sup+', [status(thm)], ['23', '24'])).
% 1.13/1.35  thf('26', plain,
% 1.13/1.35      (![X0 : $i]:
% 1.13/1.35         (r1_tarski @ (k3_xboole_0 @ sk_A @ X0) @ (k3_xboole_0 @ sk_B @ X0))),
% 1.13/1.35      inference('sup+', [status(thm)], ['22', '25'])).
% 1.13/1.35  thf('27', plain,
% 1.13/1.35      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_C_1) @ (k1_tarski @ sk_D_1))),
% 1.13/1.35      inference('sup+', [status(thm)], ['11', '26'])).
% 1.13/1.35  thf('28', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.35  thf('29', plain,
% 1.13/1.35      ((r1_tarski @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ (k1_tarski @ sk_D_1))),
% 1.13/1.35      inference('demod', [status(thm)], ['27', '28'])).
% 1.13/1.35  thf('30', plain,
% 1.13/1.35      (![X12 : $i, X13 : $i]:
% 1.13/1.35         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 1.13/1.35      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.13/1.35  thf('31', plain,
% 1.13/1.35      (((k2_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ (k1_tarski @ sk_D_1))
% 1.13/1.35         = (k1_tarski @ sk_D_1))),
% 1.13/1.35      inference('sup-', [status(thm)], ['29', '30'])).
% 1.13/1.35  thf('32', plain,
% 1.13/1.35      (![X20 : $i, X21 : $i]:
% 1.13/1.35         ((k3_xboole_0 @ X20 @ (k2_xboole_0 @ X20 @ X21)) = (X20))),
% 1.13/1.35      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.13/1.35  thf('33', plain,
% 1.13/1.35      (((k3_xboole_0 @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ (k1_tarski @ sk_D_1))
% 1.13/1.35         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.13/1.35      inference('sup+', [status(thm)], ['31', '32'])).
% 1.13/1.35  thf('34', plain,
% 1.13/1.35      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.13/1.35         ((k3_xboole_0 @ (k3_xboole_0 @ X14 @ X15) @ X16)
% 1.13/1.35           = (k3_xboole_0 @ X14 @ (k3_xboole_0 @ X15 @ X16)))),
% 1.13/1.35      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.13/1.35  thf('35', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf(l22_zfmisc_1, axiom,
% 1.13/1.35    (![A:$i,B:$i]:
% 1.13/1.35     ( ( r2_hidden @ A @ B ) =>
% 1.13/1.35       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 1.13/1.35  thf('36', plain,
% 1.13/1.35      (![X37 : $i, X38 : $i]:
% 1.13/1.35         (((k2_xboole_0 @ (k1_tarski @ X38) @ X37) = (X37))
% 1.13/1.35          | ~ (r2_hidden @ X38 @ X37))),
% 1.13/1.35      inference('cnf', [status(esa)], [l22_zfmisc_1])).
% 1.13/1.35  thf('37', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (sk_A))),
% 1.13/1.35      inference('sup-', [status(thm)], ['35', '36'])).
% 1.13/1.35  thf('38', plain,
% 1.13/1.35      (![X20 : $i, X21 : $i]:
% 1.13/1.35         ((k3_xboole_0 @ X20 @ (k2_xboole_0 @ X20 @ X21)) = (X20))),
% 1.13/1.35      inference('cnf', [status(esa)], [t21_xboole_1])).
% 1.13/1.35  thf('39', plain,
% 1.13/1.35      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (k1_tarski @ sk_D_1))),
% 1.13/1.35      inference('sup+', [status(thm)], ['37', '38'])).
% 1.13/1.35  thf('40', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.35  thf('41', plain,
% 1.13/1.35      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)) = (k1_tarski @ sk_D_1))),
% 1.13/1.35      inference('demod', [status(thm)], ['39', '40'])).
% 1.13/1.35  thf('42', plain,
% 1.13/1.35      (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D_1))
% 1.13/1.35         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.13/1.35      inference('demod', [status(thm)], ['33', '34', '41'])).
% 1.13/1.35  thf('43', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 1.13/1.35      inference('sup+', [status(thm)], ['10', '42'])).
% 1.13/1.35  thf('44', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D_1))),
% 1.13/1.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.13/1.35  thf('45', plain,
% 1.13/1.35      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.13/1.35      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.13/1.35  thf('46', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) != (k1_tarski @ sk_D_1))),
% 1.13/1.35      inference('demod', [status(thm)], ['44', '45'])).
% 1.13/1.35  thf('47', plain, ($false),
% 1.13/1.35      inference('simplify_reflect-', [status(thm)], ['43', '46'])).
% 1.13/1.35  
% 1.13/1.35  % SZS output end Refutation
% 1.13/1.35  
% 1.13/1.36  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
