%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dI8ZHljzRG

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:55 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :   37 (  38 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :  216 ( 226 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t99_zfmisc_1,conjecture,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t99_zfmisc_1])).

thf('0',plain,(
    ( k3_tarski @ ( k1_zfmisc_1 @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( X22 != X21 )
      | ( r2_hidden @ X22 @ X23 )
      | ( X23
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('2',plain,(
    ! [X21: $i] :
      ( r2_hidden @ X21 @ ( k1_tarski @ X21 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X49: $i] :
      ( r1_tarski @ ( k1_tarski @ X49 ) @ ( k1_zfmisc_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t92_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('7',plain,(
    ! [X50: $i,X51: $i] :
      ( ( r1_tarski @ X50 @ ( k3_tarski @ X51 ) )
      | ~ ( r2_hidden @ X50 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t92_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X8: $i] :
      ( ( X6 = X8 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t94_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k3_tarski @ A ) @ B ) ) )).

thf('11',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X52 ) @ X53 )
      | ( r2_hidden @ ( sk_C_3 @ X53 @ X52 ) @ X52 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X30 @ X29 )
      | ( r1_tarski @ X30 @ X28 )
      | ( X29
       != ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('13',plain,(
    ! [X28: $i,X30: $i] :
      ( ( r1_tarski @ X30 @ X28 )
      | ~ ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X1 )
      | ( r1_tarski @ ( sk_C_3 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X52: $i,X53: $i] :
      ( ( r1_tarski @ ( k3_tarski @ X52 ) @ X53 )
      | ~ ( r1_tarski @ ( sk_C_3 @ X53 @ X52 ) @ X53 ) ) ),
    inference(cnf,[status(esa)],[t94_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('19',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dI8ZHljzRG
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:53:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.54/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.72  % Solved by: fo/fo7.sh
% 0.54/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.72  % done 953 iterations in 0.264s
% 0.54/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.72  % SZS output start Refutation
% 0.54/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.54/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.72  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.54/0.72  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.54/0.72  thf(t99_zfmisc_1, conjecture,
% 0.54/0.72    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.54/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.72    (~( ![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ) )),
% 0.54/0.72    inference('cnf.neg', [status(esa)], [t99_zfmisc_1])).
% 0.54/0.72  thf('0', plain, (((k3_tarski @ (k1_zfmisc_1 @ sk_A)) != (sk_A))),
% 0.54/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.72  thf(d1_tarski, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.54/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.54/0.72  thf('1', plain,
% 0.54/0.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.54/0.72         (((X22) != (X21))
% 0.54/0.72          | (r2_hidden @ X22 @ X23)
% 0.54/0.72          | ((X23) != (k1_tarski @ X21)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d1_tarski])).
% 0.54/0.72  thf('2', plain, (![X21 : $i]: (r2_hidden @ X21 @ (k1_tarski @ X21))),
% 0.54/0.72      inference('simplify', [status(thm)], ['1'])).
% 0.54/0.72  thf(t80_zfmisc_1, axiom,
% 0.54/0.72    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.54/0.72  thf('3', plain,
% 0.54/0.72      (![X49 : $i]: (r1_tarski @ (k1_tarski @ X49) @ (k1_zfmisc_1 @ X49))),
% 0.54/0.72      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.54/0.72  thf(d3_tarski, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.72  thf('4', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.54/0.72          | (r2_hidden @ X0 @ X2)
% 0.54/0.72          | ~ (r1_tarski @ X1 @ X2))),
% 0.54/0.72      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.72  thf('5', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 0.54/0.72          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['3', '4'])).
% 0.54/0.72  thf('6', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['2', '5'])).
% 0.54/0.72  thf(t92_zfmisc_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.54/0.72  thf('7', plain,
% 0.54/0.72      (![X50 : $i, X51 : $i]:
% 0.54/0.72         ((r1_tarski @ X50 @ (k3_tarski @ X51)) | ~ (r2_hidden @ X50 @ X51))),
% 0.54/0.72      inference('cnf', [status(esa)], [t92_zfmisc_1])).
% 0.54/0.72  thf('8', plain,
% 0.54/0.72      (![X0 : $i]: (r1_tarski @ X0 @ (k3_tarski @ (k1_zfmisc_1 @ X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['6', '7'])).
% 0.54/0.72  thf(d10_xboole_0, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.54/0.72  thf('9', plain,
% 0.54/0.72      (![X6 : $i, X8 : $i]:
% 0.54/0.72         (((X6) = (X8)) | ~ (r1_tarski @ X8 @ X6) | ~ (r1_tarski @ X6 @ X8))),
% 0.54/0.72      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.54/0.72  thf('10', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         (~ (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.54/0.72          | ((k3_tarski @ (k1_zfmisc_1 @ X0)) = (X0)))),
% 0.54/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.72  thf(t94_zfmisc_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ C @ B ) ) ) =>
% 0.54/0.72       ( r1_tarski @ ( k3_tarski @ A ) @ B ) ))).
% 0.54/0.72  thf('11', plain,
% 0.54/0.72      (![X52 : $i, X53 : $i]:
% 0.54/0.72         ((r1_tarski @ (k3_tarski @ X52) @ X53)
% 0.54/0.72          | (r2_hidden @ (sk_C_3 @ X53 @ X52) @ X52))),
% 0.54/0.72      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.54/0.72  thf(d1_zfmisc_1, axiom,
% 0.54/0.72    (![A:$i,B:$i]:
% 0.54/0.72     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.54/0.72       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.54/0.72  thf('12', plain,
% 0.54/0.72      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.72         (~ (r2_hidden @ X30 @ X29)
% 0.54/0.72          | (r1_tarski @ X30 @ X28)
% 0.54/0.72          | ((X29) != (k1_zfmisc_1 @ X28)))),
% 0.54/0.72      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.54/0.72  thf('13', plain,
% 0.54/0.72      (![X28 : $i, X30 : $i]:
% 0.54/0.72         ((r1_tarski @ X30 @ X28) | ~ (r2_hidden @ X30 @ (k1_zfmisc_1 @ X28)))),
% 0.54/0.72      inference('simplify', [status(thm)], ['12'])).
% 0.54/0.72  thf('14', plain,
% 0.54/0.72      (![X0 : $i, X1 : $i]:
% 0.54/0.72         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X1)
% 0.54/0.72          | (r1_tarski @ (sk_C_3 @ X1 @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['11', '13'])).
% 0.54/0.72  thf('15', plain,
% 0.54/0.72      (![X52 : $i, X53 : $i]:
% 0.54/0.72         ((r1_tarski @ (k3_tarski @ X52) @ X53)
% 0.54/0.72          | ~ (r1_tarski @ (sk_C_3 @ X53 @ X52) @ X53))),
% 0.54/0.72      inference('cnf', [status(esa)], [t94_zfmisc_1])).
% 0.54/0.72  thf('16', plain,
% 0.54/0.72      (![X0 : $i]:
% 0.54/0.72         ((r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)
% 0.54/0.72          | (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0))),
% 0.54/0.72      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.72  thf('17', plain,
% 0.54/0.72      (![X0 : $i]: (r1_tarski @ (k3_tarski @ (k1_zfmisc_1 @ X0)) @ X0)),
% 0.54/0.72      inference('simplify', [status(thm)], ['16'])).
% 0.54/0.72  thf('18', plain, (![X0 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X0)) = (X0))),
% 0.54/0.72      inference('demod', [status(thm)], ['10', '17'])).
% 0.54/0.72  thf('19', plain, (((sk_A) != (sk_A))),
% 0.54/0.72      inference('demod', [status(thm)], ['0', '18'])).
% 0.54/0.72  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.54/0.72  
% 0.54/0.72  % SZS output end Refutation
% 0.54/0.72  
% 0.54/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
