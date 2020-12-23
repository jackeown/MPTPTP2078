%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T6KyIVvsQ4

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  121 ( 135 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k10_relat_1 @ X7 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X5 @ X6 ) @ X5 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t171_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k10_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t171_relat_1])).

thf('7',plain,(
    ( k10_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    $false ),
    inference(simplify,[status(thm)],['10'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.T6KyIVvsQ4
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:25:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 9 iterations in 0.012s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.46  thf(t7_xboole_0, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.19/0.46          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.19/0.46  thf(t166_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ C ) =>
% 0.19/0.46       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.19/0.46         ( ?[D:$i]:
% 0.19/0.46           ( ( r2_hidden @ D @ B ) & 
% 0.19/0.46             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.19/0.46             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X6 @ (k10_relat_1 @ X7 @ X5))
% 0.19/0.46          | (r2_hidden @ (sk_D @ X7 @ X5 @ X6) @ X5)
% 0.19/0.46          | ~ (v1_relat_1 @ X7))),
% 0.19/0.46      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.19/0.46          | ~ (v1_relat_1 @ X1)
% 0.19/0.46          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.19/0.46             X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.19/0.46  thf('3', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.19/0.46      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.19/0.46  thf(l24_zfmisc_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (r1_xboole_0 @ (k1_tarski @ X2) @ X3) | ~ (r2_hidden @ X2 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.19/0.46  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X0)
% 0.19/0.46          | ((k10_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['2', '5'])).
% 0.19/0.46  thf(t171_relat_1, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) =>
% 0.19/0.46       ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( v1_relat_1 @ A ) =>
% 0.19/0.46          ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t171_relat_1])).
% 0.19/0.46  thf('7', plain, (((k10_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('8', plain, ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.46  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('10', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf('11', plain, ($false), inference('simplify', [status(thm)], ['10'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
