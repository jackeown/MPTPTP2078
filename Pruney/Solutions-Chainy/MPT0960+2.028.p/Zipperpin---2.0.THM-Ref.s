%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F8ZRqY23z9

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  57 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  383 ( 485 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X14
       != ( k1_wellord2 @ X13 ) )
      | ( ( k3_relat_1 @ X14 )
        = X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X13: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X13 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
        = X13 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X13: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X6 ) @ ( sk_D @ X5 @ X6 ) ) @ X6 )
      | ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X10 @ ( k3_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X13: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X13 ) )
      = X13 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X6 ) @ ( sk_D @ X5 @ X6 ) ) @ X6 )
      | ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ ( k3_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D @ X1 @ ( k1_wellord2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_wellord2 @ X0 ) ) @ ( sk_D @ X3 @ ( k1_wellord2 @ X2 ) ) ) @ ( k2_zfmisc_1 @ X0 @ X2 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['11','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X6 ) @ ( sk_D @ X5 @ X6 ) ) @ X5 )
      | ( r1_tarski @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.F8ZRqY23z9
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 29 iterations in 0.031s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.48  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.48  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(t33_wellord2, conjecture,
% 0.21/0.48    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d1_wellord2, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.21/0.48         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.48           ( ![C:$i,D:$i]:
% 0.21/0.48             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.48               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.48                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         (((X14) != (k1_wellord2 @ X13))
% 0.21/0.48          | ((k3_relat_1 @ X14) = (X13))
% 0.21/0.48          | ~ (v1_relat_1 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X13 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ (k1_wellord2 @ X13))
% 0.21/0.48          | ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['1'])).
% 0.21/0.48  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.48  thf('3', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.48  thf('4', plain, (![X13 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf(d3_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.48           ( ![C:$i,D:$i]:
% 0.21/0.48             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.21/0.48               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         ((r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X6) @ (sk_D @ X5 @ X6)) @ X6)
% 0.21/0.48          | (r1_tarski @ X6 @ X5)
% 0.21/0.48          | ~ (v1_relat_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.48  thf(t30_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ C ) =>
% 0.21/0.48       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.21/0.48         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.21/0.48           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.21/0.48          | (r2_hidden @ X10 @ (k3_relat_1 @ X12))
% 0.21/0.48          | ~ (v1_relat_1 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | (r1_tarski @ X0 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.48          | (r1_tarski @ X0 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.48          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '8'])).
% 0.21/0.48  thf('10', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_C @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.48          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.48  thf('12', plain, (![X13 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X13)) = (X13))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         ((r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X6) @ (sk_D @ X5 @ X6)) @ X6)
% 0.21/0.48          | (r1_tarski @ X6 @ X5)
% 0.21/0.48          | ~ (v1_relat_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 0.21/0.48          | (r2_hidden @ X11 @ (k3_relat_1 @ X12))
% 0.21/0.48          | ~ (v1_relat_1 @ X12))),
% 0.21/0.48      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X0)
% 0.21/0.48          | (r1_tarski @ X0 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ X0)
% 0.21/0.48          | (r2_hidden @ (sk_D @ X1 @ X0) @ (k3_relat_1 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_D @ X1 @ X0) @ (k3_relat_1 @ X0))
% 0.21/0.48          | (r1_tarski @ X0 @ X1)
% 0.21/0.48          | ~ (v1_relat_1 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_D @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.48          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.48          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['12', '16'])).
% 0.21/0.48  thf('18', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r2_hidden @ (sk_D @ X1 @ (k1_wellord2 @ X0)) @ X0)
% 0.21/0.48          | (r1_tarski @ (k1_wellord2 @ X0) @ X1))),
% 0.21/0.48      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf(l54_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.21/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X4 : $i]:
% 0.21/0.48         ((r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X4))
% 0.21/0.48          | ~ (r2_hidden @ X2 @ X4)
% 0.21/0.48          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_wellord2 @ X0) @ X1)
% 0.21/0.48          | ~ (r2_hidden @ X3 @ X2)
% 0.21/0.48          | (r2_hidden @ (k4_tarski @ X3 @ (sk_D @ X1 @ (k1_wellord2 @ X0))) @ 
% 0.21/0.48             (k2_zfmisc_1 @ X2 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_wellord2 @ X0) @ X1)
% 0.21/0.48          | (r2_hidden @ 
% 0.21/0.48             (k4_tarski @ (sk_C @ X1 @ (k1_wellord2 @ X0)) @ 
% 0.21/0.48              (sk_D @ X3 @ (k1_wellord2 @ X2))) @ 
% 0.21/0.48             (k2_zfmisc_1 @ X0 @ X2))
% 0.21/0.48          | (r1_tarski @ (k1_wellord2 @ X2) @ X3))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X5 : $i, X6 : $i]:
% 0.21/0.48         (~ (r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X6) @ (sk_D @ X5 @ X6)) @ X5)
% 0.21/0.48          | (r1_tarski @ X6 @ X5)
% 0.21/0.48          | ~ (v1_relat_1 @ X6))),
% 0.21/0.48      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.21/0.48          | (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.21/0.48          | ~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.21/0.48          | (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.48  thf('25', plain, (![X17 : $i]: (v1_relat_1 @ (k1_wellord2 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.48  thf('26', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.21/0.48          | (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.21/0.48          | (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.21/0.48      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.48  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
