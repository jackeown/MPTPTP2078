%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Lcen1FnCv

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:53 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    9
%              Number of atoms          :  293 ( 344 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   11 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t97_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t97_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_tarski @ sk_A ) @ ( k3_tarski @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X13 ) @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ ( k3_tarski @ X12 ) )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X13 ) @ X14 )
      | ~ ( r1_tarski @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X13 ) @ X14 )
      | ( r2_hidden @ ( sk_C @ X14 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('11',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ ( k3_tarski @ X12 ) )
      | ~ ( r2_hidden @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 )
      | ( r1_tarski @ ( sk_C @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X13 ) @ X14 )
      | ~ ( r1_tarski @ ( sk_C @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_tarski @ X0 ) )
      | ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_tarski @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_tarski @ X1 ) @ ( k3_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Lcen1FnCv
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:27:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 74 iterations in 0.054s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.50  thf(t97_zfmisc_1, conjecture,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( r1_tarski @
% 0.19/0.50       ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.19/0.50       ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i]:
% 0.19/0.50        ( r1_tarski @
% 0.19/0.50          ( k3_tarski @ ( k3_xboole_0 @ A @ B ) ) @ 
% 0.19/0.50          ( k3_xboole_0 @ ( k3_tarski @ A ) @ ( k3_tarski @ B ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t97_zfmisc_1])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (~ (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 0.19/0.50          (k3_xboole_0 @ (k3_tarski @ sk_A) @ (k3_tarski @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(t94_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.19/0.50       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      (![X13 : $i, X14 : $i]:
% 0.19/0.50         ((r1_tarski @ (k3_tarski @ X13) @ X14)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.19/0.50  thf(d4_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.19/0.50       ( ![D:$i]:
% 0.19/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.50           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.50          | (r2_hidden @ X4 @ X2)
% 0.19/0.50          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.50         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '3'])).
% 0.19/0.50  thf(l49_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i]:
% 0.19/0.50         ((r1_tarski @ X11 @ (k3_tarski @ X12)) | ~ (r2_hidden @ X11 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.19/0.50          | (r1_tarski @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.19/0.50             (k3_tarski @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X13 : $i, X14 : $i]:
% 0.19/0.50         ((r1_tarski @ (k3_tarski @ X13) @ X14)
% 0.19/0.50          | ~ (r1_tarski @ (sk_C @ X14 @ X13) @ X14))),
% 0.19/0.50      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ (k3_tarski @ X0))
% 0.19/0.50          | (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.19/0.50             (k3_tarski @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ (k3_tarski @ X0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      (![X13 : $i, X14 : $i]:
% 0.19/0.50         ((r1_tarski @ (k3_tarski @ X13) @ X14)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X14 @ X13) @ X13))),
% 0.19/0.50      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.50          | (r2_hidden @ X4 @ X1)
% 0.19/0.50          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.50         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ X2)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ X1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['10', '12'])).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X11 : $i, X12 : $i]:
% 0.19/0.50         ((r1_tarski @ X11 @ (k3_tarski @ X12)) | ~ (r2_hidden @ X11 @ X12))),
% 0.19/0.50      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ X2)
% 0.19/0.50          | (r1_tarski @ (sk_C @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.19/0.50             (k3_tarski @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('16', plain,
% 0.19/0.50      (![X13 : $i, X14 : $i]:
% 0.19/0.50         ((r1_tarski @ (k3_tarski @ X13) @ X14)
% 0.19/0.50          | ~ (r1_tarski @ (sk_C @ X14 @ X13) @ X14))),
% 0.19/0.50      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ (k3_tarski @ X0))
% 0.19/0.50          | (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.19/0.50             (k3_tarski @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ (k3_tarski @ X0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.50  thf(t19_xboole_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.19/0.50       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.19/0.50         (~ (r1_tarski @ X6 @ X7)
% 0.19/0.50          | ~ (r1_tarski @ X6 @ X8)
% 0.19/0.50          | (r1_tarski @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.19/0.50      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ 
% 0.19/0.50           (k3_xboole_0 @ (k3_tarski @ X0) @ X2))
% 0.19/0.50          | ~ (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (r1_tarski @ (k3_tarski @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.19/0.50          (k3_xboole_0 @ (k3_tarski @ X1) @ (k3_tarski @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['9', '20'])).
% 0.19/0.50  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
