%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DCIQk1ttq9

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:28 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  145 ( 161 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X39: $i,X40: $i] :
      ( r1_tarski @ ( k1_tarski @ X39 ) @ ( k2_tarski @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t55_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          & ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t55_zfmisc_1])).

thf('1',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
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
    r1_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['0','9'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('11',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
      | ~ ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('12',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DCIQk1ttq9
% 0.13/0.31  % Computer   : n022.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % DateTime   : Tue Dec  1 14:16:26 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running portfolio for 600 s
% 0.13/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.32  % Number of cores: 8
% 0.13/0.32  % Python version: Python 3.6.8
% 0.13/0.32  % Running in FO mode
% 0.18/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.46  % Solved by: fo/fo7.sh
% 0.18/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.46  % done 25 iterations in 0.014s
% 0.18/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.46  % SZS output start Refutation
% 0.18/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.18/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.18/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.18/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.18/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.46  thf(t12_zfmisc_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.18/0.46  thf('0', plain,
% 0.18/0.46      (![X39 : $i, X40 : $i]:
% 0.18/0.46         (r1_tarski @ (k1_tarski @ X39) @ (k2_tarski @ X39 @ X40))),
% 0.18/0.46      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.18/0.46  thf(t55_zfmisc_1, conjecture,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.18/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.46    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.46        ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & 
% 0.18/0.46             ( r2_hidden @ A @ C ) ) ) )),
% 0.18/0.46    inference('cnf.neg', [status(esa)], [t55_zfmisc_1])).
% 0.18/0.46  thf('1', plain, ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf(symmetry_r1_xboole_0, axiom,
% 0.18/0.46    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.18/0.46  thf('2', plain,
% 0.18/0.46      (![X3 : $i, X4 : $i]:
% 0.18/0.46         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.18/0.46      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.18/0.46  thf('3', plain, ((r1_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))),
% 0.18/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.18/0.46  thf(d7_xboole_0, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.18/0.46       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.18/0.46  thf('4', plain,
% 0.18/0.46      (![X0 : $i, X1 : $i]:
% 0.18/0.46         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.18/0.46      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.18/0.46  thf('5', plain,
% 0.18/0.46      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.18/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.18/0.46  thf(t77_xboole_1, axiom,
% 0.18/0.46    (![A:$i,B:$i,C:$i]:
% 0.18/0.46     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.18/0.46          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.18/0.46  thf('6', plain,
% 0.18/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.18/0.46         ((r1_xboole_0 @ X6 @ X7)
% 0.18/0.46          | ~ (r1_xboole_0 @ X6 @ (k3_xboole_0 @ X7 @ X8))
% 0.18/0.46          | ~ (r1_tarski @ X6 @ X8))),
% 0.18/0.46      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.18/0.46  thf('7', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.18/0.46          | ~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.18/0.46          | (r1_xboole_0 @ X0 @ sk_C))),
% 0.18/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.18/0.46  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.18/0.46  thf('8', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.18/0.46      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.18/0.46  thf('9', plain,
% 0.18/0.46      (![X0 : $i]:
% 0.18/0.46         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.18/0.46          | (r1_xboole_0 @ X0 @ sk_C))),
% 0.18/0.46      inference('demod', [status(thm)], ['7', '8'])).
% 0.18/0.46  thf('10', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_C)),
% 0.18/0.46      inference('sup-', [status(thm)], ['0', '9'])).
% 0.18/0.46  thf(l24_zfmisc_1, axiom,
% 0.18/0.46    (![A:$i,B:$i]:
% 0.18/0.46     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.18/0.46  thf('11', plain,
% 0.18/0.46      (![X37 : $i, X38 : $i]:
% 0.18/0.46         (~ (r1_xboole_0 @ (k1_tarski @ X37) @ X38) | ~ (r2_hidden @ X37 @ X38))),
% 0.18/0.46      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.18/0.46  thf('12', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.18/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.18/0.46  thf('13', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.18/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.46  thf('14', plain, ($false), inference('demod', [status(thm)], ['12', '13'])).
% 0.18/0.46  
% 0.18/0.46  % SZS output end Refutation
% 0.18/0.46  
% 0.18/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
