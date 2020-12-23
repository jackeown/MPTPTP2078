%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OSdDR8kqEv

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  45 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :  167 ( 183 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k9_relat_1 @ X35 @ X33 ) )
      | ( r2_hidden @ ( sk_D @ X35 @ X33 @ X34 ) @ X33 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( r1_xboole_0 @ X4 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X29 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X29 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('5',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_xboole_0 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ( X5 = X6 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(t149_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k9_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t149_relat_1])).

thf('8',plain,(
    ( k9_relat_1 @ sk_A_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_A_1 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_A_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('11',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('12',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('13',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('14',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['11','14'])).

thf('16',plain,(
    ~ ( v1_xboole_0 @ ( k9_relat_1 @ sk_A_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,(
    ~ ( v1_relat_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OSdDR8kqEv
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 51 iterations in 0.036s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(d1_xboole_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.49  thf(t143_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.49         ( ?[D:$i]:
% 0.20/0.49           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.49             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.49             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X34 @ (k9_relat_1 @ X35 @ X33))
% 0.20/0.49          | (r2_hidden @ (sk_D @ X35 @ X33 @ X34) @ X33)
% 0.20/0.49          | ~ (v1_relat_1 @ X35))),
% 0.20/0.49      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r2_hidden @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.20/0.49             X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.49  thf('3', plain, (![X4 : $i]: (r1_xboole_0 @ X4 @ k1_xboole_0)),
% 0.20/0.49      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.49  thf(t55_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ (k2_tarski @ X29 @ X30) @ X31)
% 0.20/0.49          | ~ (r2_hidden @ X29 @ X31))),
% 0.20/0.49      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.20/0.49  thf('5', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.49  thf(t8_boole, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (v1_xboole_0 @ X5) | ~ (v1_xboole_0 @ X6) | ((X5) = (X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t8_boole])).
% 0.20/0.49  thf(t149_relat_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( v1_relat_1 @ A ) =>
% 0.20/0.49          ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t149_relat_1])).
% 0.20/0.49  thf('8', plain, (((k9_relat_1 @ sk_A_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((X0) != (k1_xboole_0))
% 0.20/0.49          | ~ (v1_xboole_0 @ (k9_relat_1 @ sk_A_1 @ k1_xboole_0))
% 0.20/0.49          | ~ (v1_xboole_0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.20/0.49        | ~ (v1_xboole_0 @ (k9_relat_1 @ sk_A_1 @ k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.49  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.20/0.49  thf('11', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.20/0.49  thf('12', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.20/0.49  thf(l13_xboole_0, axiom,
% 0.20/0.49    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.49  thf('14', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.49      inference('demod', [status(thm)], ['11', '14'])).
% 0.20/0.49  thf('16', plain, (~ (v1_xboole_0 @ (k9_relat_1 @ sk_A_1 @ k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '15'])).
% 0.20/0.49  thf('17', plain, (~ (v1_relat_1 @ sk_A_1)),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '16'])).
% 0.20/0.49  thf('18', plain, ((v1_relat_1 @ sk_A_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain, ($false), inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
