%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9iRCfdCeFo

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (  78 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  370 ( 617 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ ( k1_tarski @ X24 ) )
        = X23 )
      | ( r2_hidden @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X20 @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('9',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r1_xboole_0 @ sk_C_1 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
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

thf('17',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('22',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( X6 != X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X17 @ X18 )
      | ~ ( r1_xboole_0 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('31',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i] :
      ( r1_tarski @ X7 @ X7 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('38',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9iRCfdCeFo
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:20:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 238 iterations in 0.104s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.56  thf(t149_zfmisc_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.21/0.56         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.21/0.56       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.21/0.56            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.21/0.56          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.21/0.56  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.56  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.21/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.56  thf(t65_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.21/0.56       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X23 : $i, X24 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X23 @ (k1_tarski @ X24)) = (X23))
% 0.21/0.56          | (r2_hidden @ X24 @ X23))),
% 0.21/0.56      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.21/0.56  thf(t79_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X20 : $i, X21 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X20 @ X21) @ X21)),
% 0.21/0.56      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X0 @ (k1_tarski @ X1)) | (r2_hidden @ X1 @ X0))),
% 0.21/0.56      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.56  thf(t70_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.21/0.56            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.21/0.56       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.21/0.56            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X13 @ X14)
% 0.21/0.56          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.21/0.56          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.56  thf('11', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('12', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.21/0.56          | ~ (r1_xboole_0 @ X13 @ X14)
% 0.21/0.56          | ~ (r1_xboole_0 @ X13 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r1_xboole_0 @ sk_C_1 @ X0)
% 0.21/0.56          | (r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.56  thf('15', plain, ((r1_xboole_0 @ sk_C_1 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['11', '14'])).
% 0.21/0.56  thf('16', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(t3_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.56            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X4 @ X2)
% 0.21/0.56          | ~ (r2_hidden @ X4 @ X5)
% 0.21/0.56          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.21/0.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.21/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.56  thf('19', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.56  thf('20', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '19'])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.56  thf('22', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 0.21/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf(d10_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X6 : $i, X7 : $i]: ((r1_tarski @ X6 @ X7) | ((X6) != (X7)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.56  thf('25', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.21/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.56  thf(t64_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.21/0.56         ( r1_xboole_0 @ B @ D ) ) =>
% 0.21/0.56       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.56  thf('26', plain,
% 0.21/0.56      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X9 @ X10)
% 0.21/0.56          | ~ (r1_tarski @ X9 @ X11)
% 0.21/0.56          | ~ (r1_tarski @ X10 @ X12)
% 0.21/0.56          | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.21/0.56  thf('27', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.56          | ~ (r1_tarski @ X2 @ X1)
% 0.21/0.56          | (r1_xboole_0 @ X0 @ X2))),
% 0.21/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.56  thf('28', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B))
% 0.21/0.56          | ~ (r1_xboole_0 @ X0 @ (k1_tarski @ sk_D)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['23', '27'])).
% 0.21/0.56  thf('29', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '28'])).
% 0.21/0.56  thf(t77_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.56          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.21/0.56  thf('30', plain,
% 0.21/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X17 @ X18)
% 0.21/0.56          | ~ (r1_xboole_0 @ X17 @ (k3_xboole_0 @ X18 @ X19))
% 0.21/0.56          | ~ (r1_tarski @ X17 @ X19))),
% 0.21/0.56      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.21/0.56  thf('31', plain,
% 0.21/0.56      ((~ (r1_tarski @ sk_B @ sk_B) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.56      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.56  thf('32', plain, (![X7 : $i]: (r1_tarski @ X7 @ X7)),
% 0.21/0.56      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.56  thf('33', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.21/0.56      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.56  thf('34', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 0.21/0.56          | ~ (r1_xboole_0 @ X13 @ X14)
% 0.21/0.56          | ~ (r1_xboole_0 @ X13 @ X15))),
% 0.21/0.56      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.21/0.56  thf('35', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.21/0.56          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.56  thf('36', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '35'])).
% 0.21/0.56  thf('37', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.56      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.56  thf('38', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.21/0.56      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.56  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.21/0.56  
% 0.21/0.56  % SZS output end Refutation
% 0.21/0.56  
% 0.21/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
