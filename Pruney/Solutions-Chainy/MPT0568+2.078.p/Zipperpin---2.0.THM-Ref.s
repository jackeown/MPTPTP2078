%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yPtnaBzWhD

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:58 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   46 (  53 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :  207 ( 242 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('5',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('simplify_reflect+',[status(thm)],['7','8'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ ( k10_relat_1 @ X8 @ X6 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X6 @ X7 ) @ ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_B @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('15',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_B @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['9','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yPtnaBzWhD
% 0.14/0.37  % Computer   : n024.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:24:36 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 427 iterations in 0.180s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.66  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.45/0.66  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.45/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.45/0.66  thf(t7_xboole_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.66          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X3) @ X3))),
% 0.45/0.66      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.66  thf(d1_xboole_0, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.66  thf('3', plain,
% 0.45/0.66      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.66      inference('sup+', [status(thm)], ['2', '3'])).
% 0.45/0.66  thf(t172_relat_1, conjecture,
% 0.45/0.66    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.45/0.66  thf('5', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((X0) != (k1_xboole_0))
% 0.45/0.66          | ~ (v1_xboole_0 @ X0)
% 0.45/0.66          | ~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      ((~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))
% 0.45/0.66        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.45/0.66      inference('simplify', [status(thm)], ['6'])).
% 0.45/0.66  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.66  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.66  thf('9', plain, (~ (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.45/0.66      inference('simplify_reflect+', [status(thm)], ['7', '8'])).
% 0.45/0.66  thf(t60_relat_1, axiom,
% 0.45/0.66    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.66     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf('10', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.66  thf(t166_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ C ) =>
% 0.45/0.66       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.45/0.66         ( ?[D:$i]:
% 0.45/0.66           ( ( r2_hidden @ D @ B ) & 
% 0.45/0.66             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.45/0.66             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X7 @ (k10_relat_1 @ X8 @ X6))
% 0.45/0.66          | (r2_hidden @ (sk_D @ X8 @ X6 @ X7) @ (k2_relat_1 @ X8))
% 0.45/0.66          | ~ (v1_relat_1 @ X8))),
% 0.45/0.66      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((v1_xboole_0 @ (k10_relat_1 @ X1 @ X0))
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k10_relat_1 @ X1 @ X0))) @ 
% 0.45/0.66             (k2_relat_1 @ X1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['11', '12'])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((r2_hidden @ 
% 0.45/0.66           (sk_D @ k1_xboole_0 @ X0 @ (sk_B @ (k10_relat_1 @ k1_xboole_0 @ X0))) @ 
% 0.45/0.66           k1_xboole_0)
% 0.45/0.66          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.66          | (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.45/0.66      inference('sup+', [status(thm)], ['10', '13'])).
% 0.45/0.66  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.45/0.66  thf('15', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.45/0.66  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.45/0.66  thf('16', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.45/0.66  thf('17', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.66      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf('18', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((r2_hidden @ 
% 0.45/0.66           (sk_D @ k1_xboole_0 @ X0 @ (sk_B @ (k10_relat_1 @ k1_xboole_0 @ X0))) @ 
% 0.45/0.66           k1_xboole_0)
% 0.45/0.66          | (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0)))),
% 0.45/0.66      inference('demod', [status(thm)], ['14', '17'])).
% 0.45/0.66  thf('19', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.45/0.66      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.45/0.66  thf('20', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         ((v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))
% 0.45/0.66          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.45/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.66  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.66      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.66  thf('22', plain,
% 0.45/0.66      (![X0 : $i]: (v1_xboole_0 @ (k10_relat_1 @ k1_xboole_0 @ X0))),
% 0.45/0.66      inference('demod', [status(thm)], ['20', '21'])).
% 0.45/0.66  thf('23', plain, ($false), inference('demod', [status(thm)], ['9', '22'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
