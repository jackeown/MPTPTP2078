%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YkOZ8d3Jxn

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   19 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  152 ( 152 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t150_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k9_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t150_relat_1])).

thf('0',plain,(
    ( k9_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ ( k9_relat_1 @ X15 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X15 @ X13 @ X14 ) @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X1 @ X0 @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ ( sk_B @ ( k9_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ( ( k4_xboole_0 @ X9 @ ( k1_tarski @ X8 ) )
       != X9 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('9',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YkOZ8d3Jxn
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:42:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 31 iterations in 0.023s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.49  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.49  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.49  thf(t150_relat_1, conjecture,
% 0.22/0.49    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.22/0.49  thf('0', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t7_xboole_0, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.49  thf(t143_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ C ) =>
% 0.22/0.49       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.22/0.49         ( ?[D:$i]:
% 0.22/0.49           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.49             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.22/0.49             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X14 @ (k9_relat_1 @ X15 @ X13))
% 0.22/0.49          | (r2_hidden @ (k4_tarski @ (sk_D @ X15 @ X13 @ X14) @ X14) @ X15)
% 0.22/0.49          | ~ (v1_relat_1 @ X15))),
% 0.22/0.49      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (((k9_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.22/0.49          | ~ (v1_relat_1 @ X1)
% 0.22/0.49          | (r2_hidden @ 
% 0.22/0.49             (k4_tarski @ (sk_D @ X1 @ X0 @ (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.22/0.49              (sk_B @ (k9_relat_1 @ X1 @ X0))) @ 
% 0.22/0.49             X1))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.49  thf(t4_boole, axiom,
% 0.22/0.49    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X1 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t4_boole])).
% 0.22/0.49  thf(t65_zfmisc_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.22/0.49       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i]:
% 0.22/0.49         (~ (r2_hidden @ X8 @ X9)
% 0.22/0.49          | ((k4_xboole_0 @ X9 @ (k1_tarski @ X8)) != (X9)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.49  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.22/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ k1_xboole_0)
% 0.22/0.49          | ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '7'])).
% 0.22/0.49  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.49  thf('9', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.22/0.49  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.49  thf('10', plain, (![X11 : $i]: (v1_relat_1 @ (k6_relat_1 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.49  thf('11', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.49      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['8', '11'])).
% 0.22/0.49  thf('13', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.49      inference('demod', [status(thm)], ['0', '12'])).
% 0.22/0.49  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
