%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FXqezttux1

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:33 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   72 (  95 expanded)
%              Number of leaves         :   21 (  37 expanded)
%              Depth                    :   17
%              Number of atoms          :  456 ( 755 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k4_xboole_0 @ X29 @ ( k1_tarski @ X30 ) )
        = X29 )
      | ( r2_hidden @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ X16 )
      | ( ( k4_xboole_0 @ X14 @ X16 )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != X0 )
      | ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      | ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('18',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = sk_B ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('28',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['26','27'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_xboole_0 @ X17 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_A ) )
    = sk_B ),
    inference(demod,[status(thm)],['35','38'])).

thf(t90_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ) )).

thf('40',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ ( k3_xboole_0 @ X20 @ X21 ) ) @ X21 ) ),
    inference(cnf,[status(esa)],[t90_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('42',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) ) @ X21 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) )
      | ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','45'])).

thf('47',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FXqezttux1
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.86  % Solved by: fo/fo7.sh
% 0.67/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.86  % done 969 iterations in 0.411s
% 0.67/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.86  % SZS output start Refutation
% 0.67/0.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.86  thf(sk_D_type, type, sk_D: $i).
% 0.67/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.67/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.86  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.86  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.67/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.67/0.86  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.67/0.86  thf(t149_zfmisc_1, conjecture,
% 0.67/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.86     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.67/0.86         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.67/0.86       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.67/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.86    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.86        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.67/0.86            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.67/0.86          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.67/0.86    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.67/0.86  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.67/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.86  thf(symmetry_r1_xboole_0, axiom,
% 0.67/0.86    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.67/0.86  thf('2', plain,
% 0.67/0.86      (![X2 : $i, X3 : $i]:
% 0.67/0.86         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.67/0.86      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.86  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.67/0.86      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.86  thf(t65_zfmisc_1, axiom,
% 0.67/0.86    (![A:$i,B:$i]:
% 0.67/0.86     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.67/0.87       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.67/0.87  thf('4', plain,
% 0.67/0.87      (![X29 : $i, X30 : $i]:
% 0.67/0.87         (((k4_xboole_0 @ X29 @ (k1_tarski @ X30)) = (X29))
% 0.67/0.87          | (r2_hidden @ X30 @ X29))),
% 0.67/0.87      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.67/0.87  thf(t83_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.67/0.87  thf('5', plain,
% 0.67/0.87      (![X14 : $i, X16 : $i]:
% 0.67/0.87         ((r1_xboole_0 @ X14 @ X16) | ((k4_xboole_0 @ X14 @ X16) != (X14)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.67/0.87  thf('6', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         (((X0) != (X0))
% 0.67/0.87          | (r2_hidden @ X1 @ X0)
% 0.67/0.87          | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['4', '5'])).
% 0.67/0.87  thf('7', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 0.67/0.87      inference('simplify', [status(thm)], ['6'])).
% 0.67/0.87  thf('8', plain,
% 0.67/0.87      (![X2 : $i, X3 : $i]:
% 0.67/0.87         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.67/0.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.87  thf('9', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['7', '8'])).
% 0.67/0.87  thf(t70_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i]:
% 0.67/0.87     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.67/0.87            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.67/0.87       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.67/0.87            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.67/0.87  thf('10', plain,
% 0.67/0.87      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.67/0.87         ((r1_xboole_0 @ X10 @ X11)
% 0.67/0.87          | ~ (r1_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X13)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.67/0.87  thf('11', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.67/0.87         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.67/0.87          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['9', '10'])).
% 0.67/0.87  thf('12', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('13', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf('14', plain,
% 0.67/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.67/0.87         ((r1_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.67/0.87          | ~ (r1_xboole_0 @ X10 @ X11)
% 0.67/0.87          | ~ (r1_xboole_0 @ X10 @ X12))),
% 0.67/0.87      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.67/0.87  thf('15', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 0.67/0.87          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['13', '14'])).
% 0.67/0.87  thf('16', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.67/0.87      inference('sup-', [status(thm)], ['12', '15'])).
% 0.67/0.87  thf('17', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(t3_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.67/0.87            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.67/0.87       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.67/0.87            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.67/0.87  thf('18', plain,
% 0.67/0.87      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.67/0.87         (~ (r2_hidden @ X6 @ X4)
% 0.67/0.87          | ~ (r2_hidden @ X6 @ X7)
% 0.67/0.87          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.67/0.87      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.67/0.87  thf('19', plain,
% 0.67/0.87      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.67/0.87      inference('sup-', [status(thm)], ['17', '18'])).
% 0.67/0.87  thf('20', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.67/0.87      inference('sup-', [status(thm)], ['16', '19'])).
% 0.67/0.87  thf('21', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 0.67/0.87      inference('sup-', [status(thm)], ['11', '20'])).
% 0.67/0.87  thf('22', plain,
% 0.67/0.87      (![X2 : $i, X3 : $i]:
% 0.67/0.87         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.67/0.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.87  thf('23', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 0.67/0.87      inference('sup-', [status(thm)], ['21', '22'])).
% 0.67/0.87  thf('24', plain,
% 0.67/0.87      (![X14 : $i, X15 : $i]:
% 0.67/0.87         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.67/0.87      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.67/0.87  thf('25', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (sk_B))),
% 0.67/0.87      inference('sup-', [status(thm)], ['23', '24'])).
% 0.67/0.87  thf('26', plain,
% 0.67/0.87      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.67/0.87      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.87  thf(commutativity_k3_xboole_0, axiom,
% 0.67/0.87    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.67/0.87  thf('27', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.67/0.87      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.67/0.87  thf('28', plain,
% 0.67/0.87      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.67/0.87      inference('demod', [status(thm)], ['26', '27'])).
% 0.67/0.87  thf(t85_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i,C:$i]:
% 0.67/0.87     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.67/0.87  thf('29', plain,
% 0.67/0.87      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.67/0.87         (~ (r1_tarski @ X17 @ X18)
% 0.67/0.87          | (r1_xboole_0 @ X17 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.67/0.87      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.67/0.87  thf('30', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 0.67/0.87          (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['28', '29'])).
% 0.67/0.87  thf('31', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 0.67/0.87      inference('sup+', [status(thm)], ['25', '30'])).
% 0.67/0.87  thf('32', plain,
% 0.67/0.87      (![X2 : $i, X3 : $i]:
% 0.67/0.87         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.67/0.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.87  thf('33', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.67/0.87      inference('sup-', [status(thm)], ['31', '32'])).
% 0.67/0.87  thf('34', plain,
% 0.67/0.87      (![X14 : $i, X15 : $i]:
% 0.67/0.87         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.67/0.87      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.67/0.87  thf('35', plain,
% 0.67/0.87      (((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 0.67/0.87      inference('sup-', [status(thm)], ['33', '34'])).
% 0.67/0.87  thf(t48_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.67/0.87  thf('36', plain,
% 0.67/0.87      (![X8 : $i, X9 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.67/0.87           = (k3_xboole_0 @ X8 @ X9))),
% 0.67/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.87  thf('37', plain,
% 0.67/0.87      (![X8 : $i, X9 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.67/0.87           = (k3_xboole_0 @ X8 @ X9))),
% 0.67/0.87      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.67/0.87  thf('38', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.87           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.87      inference('sup+', [status(thm)], ['36', '37'])).
% 0.67/0.87  thf('39', plain,
% 0.67/0.87      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_A)) = (sk_B))),
% 0.67/0.87      inference('demod', [status(thm)], ['35', '38'])).
% 0.67/0.87  thf(t90_xboole_1, axiom,
% 0.67/0.87    (![A:$i,B:$i]:
% 0.67/0.87     ( r1_xboole_0 @ ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) @ B ))).
% 0.67/0.87  thf('40', plain,
% 0.67/0.87      (![X20 : $i, X21 : $i]:
% 0.67/0.87         (r1_xboole_0 @ (k4_xboole_0 @ X20 @ (k3_xboole_0 @ X20 @ X21)) @ X21)),
% 0.67/0.87      inference('cnf', [status(esa)], [t90_xboole_1])).
% 0.67/0.87  thf('41', plain,
% 0.67/0.87      (![X0 : $i, X1 : $i]:
% 0.67/0.87         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.67/0.87           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.67/0.87      inference('sup+', [status(thm)], ['36', '37'])).
% 0.67/0.87  thf('42', plain,
% 0.67/0.87      (![X20 : $i, X21 : $i]:
% 0.67/0.87         (r1_xboole_0 @ (k3_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21)) @ X21)),
% 0.67/0.87      inference('demod', [status(thm)], ['40', '41'])).
% 0.67/0.87  thf('43', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.67/0.87      inference('sup+', [status(thm)], ['39', '42'])).
% 0.67/0.87  thf('44', plain,
% 0.67/0.87      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.67/0.87         ((r1_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12))
% 0.67/0.87          | ~ (r1_xboole_0 @ X10 @ X11)
% 0.67/0.87          | ~ (r1_xboole_0 @ X10 @ X12))),
% 0.67/0.87      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.67/0.87  thf('45', plain,
% 0.67/0.87      (![X0 : $i]:
% 0.67/0.87         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.67/0.87          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.67/0.87      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.87  thf('46', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 0.67/0.87      inference('sup-', [status(thm)], ['3', '45'])).
% 0.67/0.87  thf('47', plain,
% 0.67/0.87      (![X2 : $i, X3 : $i]:
% 0.67/0.87         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.67/0.87      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.67/0.87  thf('48', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.67/0.87      inference('sup-', [status(thm)], ['46', '47'])).
% 0.67/0.87  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 0.67/0.87  
% 0.67/0.87  % SZS output end Refutation
% 0.67/0.87  
% 0.67/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
