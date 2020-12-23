%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AULfsIhkOu

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 (  71 expanded)
%              Number of leaves         :   17 (  28 expanded)
%              Depth                    :   15
%              Number of atoms          :  302 ( 513 expanded)
%              Number of equality atoms :    2 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['1','2'])).

thf('7',plain,(
    r2_hidden @ sk_D @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('8',plain,(
    ! [X26: $i,X28: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X26 ) @ X28 )
      | ~ ( r2_hidden @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t37_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ ( k1_tarski @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) )
      | ~ ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('16',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X12 )
      | ~ ( r1_tarski @ X11 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['5','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,(
    r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('24',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('27',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['25','26'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('28',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','29'])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AULfsIhkOu
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:19:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 269 iterations in 0.073s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(t149_zfmisc_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.21/0.50         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.21/0.50       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.21/0.50            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.21/0.50          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.21/0.50  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain, ((r1_xboole_0 @ sk_C @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.50  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf(d10_xboole_0, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.50  thf('5', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.21/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.50  thf('6', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.50  thf('7', plain, ((r2_hidden @ sk_D @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t37_zfmisc_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X26 : $i, X28 : $i]:
% 0.21/0.50         ((r1_tarski @ (k1_tarski @ X26) @ X28) | ~ (r2_hidden @ X26 @ X28))),
% 0.21/0.50      inference('cnf', [status(esa)], [t37_zfmisc_1])).
% 0.21/0.50  thf('9', plain, ((r1_tarski @ (k1_tarski @ sk_D) @ sk_C)),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.50  thf('10', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.21/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.50  thf(t64_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.21/0.50         ( r1_xboole_0 @ B @ D ) ) =>
% 0.21/0.50       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X10 @ X11)
% 0.21/0.50          | ~ (r1_tarski @ X10 @ X12)
% 0.21/0.50          | ~ (r1_tarski @ X11 @ X13)
% 0.21/0.50          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.50          | ~ (r1_tarski @ X2 @ X1)
% 0.21/0.50          | (r1_xboole_0 @ X0 @ X2))),
% 0.21/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X0 @ (k1_tarski @ sk_D)) | ~ (r1_xboole_0 @ X0 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['9', '12'])).
% 0.21/0.50  thf('14', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.50  thf('16', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X10 @ X11)
% 0.21/0.50          | ~ (r1_tarski @ X10 @ X12)
% 0.21/0.50          | ~ (r1_tarski @ X11 @ X13)
% 0.21/0.50          | ~ (r1_xboole_0 @ X12 @ X13))),
% 0.21/0.50      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X0)
% 0.21/0.50          | (r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.21/0.50          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['16', '19'])).
% 0.21/0.50  thf('21', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.50  thf('23', plain, ((r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.50  thf(t77_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.50          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X18 @ X19)
% 0.21/0.50          | ~ (r1_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20))
% 0.21/0.50          | ~ (r1_tarski @ X18 @ X20))),
% 0.21/0.50      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((~ (r1_tarski @ sk_B @ sk_B) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.50  thf('26', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.21/0.50      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.50  thf('27', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf(t70_xboole_1, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.21/0.50            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.21/0.50       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.21/0.50            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.21/0.50          | ~ (r1_xboole_0 @ X14 @ X15)
% 0.21/0.50          | ~ (r1_xboole_0 @ X14 @ X16))),
% 0.21/0.50      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.21/0.50          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['3', '29'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i]:
% 0.21/0.50         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.50  thf('32', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C) @ sk_B)),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
