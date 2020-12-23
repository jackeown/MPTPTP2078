%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VDJKQNPcLg

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:13 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   57 (  87 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :   13
%              Number of atoms          :  371 ( 672 expanded)
%              Number of equality atoms :   44 (  80 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    r2_hidden @ sk_D_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X31 ) @ X33 )
      | ~ ( r2_hidden @ X31 @ X33 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('6',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_A )
    = ( k1_tarski @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k2_xboole_0 @ X17 @ X16 )
        = X16 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('13',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ ( k2_xboole_0 @ X21 @ X22 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('15',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k3_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('21',plain,(
    ! [X12: $i] :
      ( ( k3_xboole_0 @ X12 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k3_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ sk_B )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ X0 ) @ ( k3_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k3_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k3_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = ( k3_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','30'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['9','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['8','34'])).

thf('36',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C_1 )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('38',plain,(
    ( k3_xboole_0 @ sk_C_1 @ sk_A )
 != ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VDJKQNPcLg
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:58:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.40/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.60  % Solved by: fo/fo7.sh
% 0.40/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.60  % done 275 iterations in 0.134s
% 0.40/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.60  % SZS output start Refutation
% 0.40/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.60  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.60  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.40/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.60  thf(t148_zfmisc_1, conjecture,
% 0.40/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60     ( ( ( r1_tarski @ A @ B ) & 
% 0.40/0.60         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.40/0.60         ( r2_hidden @ D @ A ) ) =>
% 0.40/0.60       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.40/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.60        ( ( ( r1_tarski @ A @ B ) & 
% 0.40/0.60            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.40/0.60            ( r2_hidden @ D @ A ) ) =>
% 0.40/0.60          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.40/0.60    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.40/0.60  thf('0', plain, ((r2_hidden @ sk_D_1 @ sk_A)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf(l1_zfmisc_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.40/0.60  thf('1', plain,
% 0.40/0.60      (![X31 : $i, X33 : $i]:
% 0.40/0.60         ((r1_tarski @ (k1_tarski @ X31) @ X33) | ~ (r2_hidden @ X31 @ X33))),
% 0.40/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.40/0.60  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_D_1) @ sk_A)),
% 0.40/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.40/0.60  thf(t12_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]:
% 0.40/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.40/0.60  thf('3', plain,
% 0.40/0.60      (![X16 : $i, X17 : $i]:
% 0.40/0.60         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.40/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.40/0.60  thf('4', plain, (((k2_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (sk_A))),
% 0.40/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.60  thf(t21_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.40/0.60  thf('5', plain,
% 0.40/0.60      (![X21 : $i, X22 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22)) = (X21))),
% 0.40/0.60      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.40/0.60  thf('6', plain,
% 0.40/0.60      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_A) = (k1_tarski @ sk_D_1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['4', '5'])).
% 0.40/0.60  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.60  thf('7', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.60  thf('8', plain,
% 0.40/0.60      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1)) = (k1_tarski @ sk_D_1))),
% 0.40/0.60      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.60  thf('9', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_tarski @ sk_D_1))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('10', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.60  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('12', plain,
% 0.40/0.60      (![X16 : $i, X17 : $i]:
% 0.40/0.60         (((k2_xboole_0 @ X17 @ X16) = (X16)) | ~ (r1_tarski @ X17 @ X16))),
% 0.40/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.40/0.60  thf('13', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.40/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.60  thf('14', plain,
% 0.40/0.60      (![X21 : $i, X22 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ X21 @ (k2_xboole_0 @ X21 @ X22)) = (X21))),
% 0.40/0.60      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.40/0.60  thf('15', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.40/0.60      inference('sup+', [status(thm)], ['13', '14'])).
% 0.40/0.60  thf('16', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.60  thf('17', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['15', '16'])).
% 0.40/0.60  thf(t16_xboole_1, axiom,
% 0.40/0.60    (![A:$i,B:$i,C:$i]:
% 0.40/0.60     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.40/0.60       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.40/0.60  thf('18', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20)
% 0.40/0.60           = (k3_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.40/0.60  thf('19', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ sk_A @ X0)
% 0.40/0.60           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['17', '18'])).
% 0.40/0.60  thf('20', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.60  thf(idempotence_k3_xboole_0, axiom,
% 0.40/0.60    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.40/0.60  thf('21', plain, (![X12 : $i]: ((k3_xboole_0 @ X12 @ X12) = (X12))),
% 0.40/0.60      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.40/0.60  thf('22', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20)
% 0.40/0.60           = (k3_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.40/0.60  thf('23', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ X0 @ X1)
% 0.40/0.60           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['21', '22'])).
% 0.40/0.60  thf('24', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ X0 @ X1)
% 0.40/0.60           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['20', '23'])).
% 0.40/0.60  thf('25', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ sk_B)
% 0.40/0.60           = (k3_xboole_0 @ (k3_xboole_0 @ sk_A @ X0) @ 
% 0.40/0.60              (k3_xboole_0 @ sk_A @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['19', '24'])).
% 0.40/0.60  thf('26', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20)
% 0.40/0.60           = (k3_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.40/0.60  thf('27', plain,
% 0.40/0.60      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X20)
% 0.40/0.60           = (k3_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.40/0.60      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.40/0.60  thf('28', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ X0 @ X1)
% 0.40/0.60           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['20', '23'])).
% 0.40/0.60  thf('29', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ X0 @ X1)
% 0.40/0.60           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.40/0.60      inference('sup+', [status(thm)], ['20', '23'])).
% 0.40/0.60  thf('30', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ X0 @ sk_B))
% 0.40/0.60           = (k3_xboole_0 @ sk_A @ X0))),
% 0.40/0.60      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.40/0.60  thf('31', plain,
% 0.40/0.60      (![X0 : $i]:
% 0.40/0.60         ((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ X0))
% 0.40/0.60           = (k3_xboole_0 @ sk_A @ X0))),
% 0.40/0.60      inference('sup+', [status(thm)], ['10', '30'])).
% 0.40/0.60  thf('32', plain,
% 0.40/0.60      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 0.40/0.60         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.40/0.60      inference('sup+', [status(thm)], ['9', '31'])).
% 0.40/0.60  thf('33', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.60  thf('34', plain,
% 0.40/0.60      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D_1))
% 0.40/0.60         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.40/0.60      inference('demod', [status(thm)], ['32', '33'])).
% 0.40/0.60  thf('35', plain, (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.40/0.60      inference('sup+', [status(thm)], ['8', '34'])).
% 0.40/0.60  thf('36', plain, (((k3_xboole_0 @ sk_A @ sk_C_1) != (k1_tarski @ sk_D_1))),
% 0.40/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.60  thf('37', plain,
% 0.40/0.60      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.60      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.60  thf('38', plain, (((k3_xboole_0 @ sk_C_1 @ sk_A) != (k1_tarski @ sk_D_1))),
% 0.40/0.60      inference('demod', [status(thm)], ['36', '37'])).
% 0.40/0.60  thf('39', plain, ($false),
% 0.40/0.60      inference('simplify_reflect-', [status(thm)], ['35', '38'])).
% 0.40/0.60  
% 0.40/0.60  % SZS output end Refutation
% 0.40/0.60  
% 0.45/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
