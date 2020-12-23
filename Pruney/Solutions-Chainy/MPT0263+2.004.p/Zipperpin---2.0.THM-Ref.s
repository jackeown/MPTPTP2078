%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pghmriojVX

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:31 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    9
%              Number of atoms          :  316 ( 390 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf('0',plain,(
    ! [X36: $i,X38: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X36 ) @ X38 )
        = ( k1_tarski @ X36 ) )
      | ( r2_hidden @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k4_xboole_0 @ X10 @ X12 )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t58_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
      | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
        | ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t58_zfmisc_1])).

thf('4',plain,(
    ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X28 @ X27 )
      | ( X28 = X25 )
      | ( X27
       != ( k1_tarski @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('9',plain,(
    ! [X25: $i,X28: $i] :
      ( ( X28 = X25 )
      | ~ ( r2_hidden @ X28 @ ( k1_tarski @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X7: $i] :
      ( ( X7
        = ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X4 @ X3 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','15'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('21',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pghmriojVX
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:35:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 300 iterations in 0.225s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(l33_zfmisc_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.68       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.45/0.68  thf('0', plain,
% 0.45/0.68      (![X36 : $i, X38 : $i]:
% 0.45/0.68         (((k4_xboole_0 @ (k1_tarski @ X36) @ X38) = (k1_tarski @ X36))
% 0.45/0.68          | (r2_hidden @ X36 @ X38))),
% 0.45/0.68      inference('cnf', [status(esa)], [l33_zfmisc_1])).
% 0.45/0.68  thf(t83_xboole_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (![X10 : $i, X12 : $i]:
% 0.45/0.68         ((r1_xboole_0 @ X10 @ X12) | ((k4_xboole_0 @ X10 @ X12) != (X10)))),
% 0.45/0.68      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.45/0.68          | (r2_hidden @ X0 @ X1)
% 0.45/0.68          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.45/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.45/0.68      inference('simplify', [status(thm)], ['2'])).
% 0.45/0.68  thf(t58_zfmisc_1, conjecture,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.45/0.68       ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i,B:$i]:
% 0.45/0.68        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) | 
% 0.45/0.68          ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t58_zfmisc_1])).
% 0.45/0.68  thf('4', plain, (~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('5', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.45/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.68  thf(d4_xboole_0, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.45/0.68       ( ![D:$i]:
% 0.45/0.68         ( ( r2_hidden @ D @ C ) <=>
% 0.45/0.68           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.45/0.68         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.45/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.45/0.68          | (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.45/0.68          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.68      inference('eq_fact', [status(thm)], ['6'])).
% 0.45/0.68  thf(d1_tarski, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.68       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X28 @ X27)
% 0.45/0.68          | ((X28) = (X25))
% 0.45/0.68          | ((X27) != (k1_tarski @ X25)))),
% 0.45/0.68      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (![X25 : $i, X28 : $i]:
% 0.45/0.68         (((X28) = (X25)) | ~ (r2_hidden @ X28 @ (k1_tarski @ X25)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['8'])).
% 0.45/0.68  thf('10', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.45/0.68          | ((sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['7', '9'])).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (![X3 : $i, X4 : $i, X7 : $i]:
% 0.45/0.68         (((X7) = (k3_xboole_0 @ X3 @ X4))
% 0.45/0.68          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X4)
% 0.45/0.68          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X3)
% 0.45/0.68          | ~ (r2_hidden @ (sk_D @ X7 @ X4 @ X3) @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.45/0.68  thf('12', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.68          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.45/0.68          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 0.45/0.68               (k1_tarski @ X0))
% 0.45/0.68          | ~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 0.45/0.68               (k1_tarski @ X0))
% 0.45/0.68          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1 @ (k1_tarski @ X0)) @ 
% 0.45/0.68             (k1_tarski @ X0))
% 0.45/0.68          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 0.45/0.68          | ~ (r2_hidden @ X0 @ X1))),
% 0.45/0.68      inference('simplify', [status(thm)], ['12'])).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.45/0.68          | ((X0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.68      inference('eq_fact', [status(thm)], ['6'])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.68          | ((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 0.45/0.68      inference('clc', [status(thm)], ['13', '14'])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (((k1_tarski @ sk_A) = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.45/0.68      inference('sup-', [status(thm)], ['5', '15'])).
% 0.45/0.68  thf(commutativity_k3_xboole_0, axiom,
% 0.45/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.45/0.68  thf('17', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.68  thf('18', plain,
% 0.45/0.68      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['16', '17'])).
% 0.45/0.68  thf('19', plain,
% 0.45/0.68      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('20', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.45/0.68      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.68  thf('22', plain, ($false),
% 0.45/0.68      inference('simplify_reflect-', [status(thm)], ['18', '21'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
