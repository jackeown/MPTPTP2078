%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DPFy50j7yQ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:36 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   47 (  54 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  286 ( 365 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t7_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( ( A = k1_xboole_0 )
          | ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_setfam_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X28 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X29 @ X28 ) @ X28 )
      | ( r1_tarski @ X29 @ ( k1_setfam_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X21 @ X22 ) @ X22 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X17 @ X18 )
      | ( r1_xboole_0 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ X23 @ X24 )
        = X23 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['2','11'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('14',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf(t4_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ) )).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_tarski @ ( k1_setfam_1 @ X26 ) @ X27 )
      | ~ ( r2_hidden @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t4_setfam_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k1_setfam_1 @ sk_A ) )
      | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( sk_C @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X28: $i,X29: $i] :
      ( ( X28 = k1_xboole_0 )
      | ~ ( r1_tarski @ X29 @ ( sk_C @ X29 @ X28 ) )
      | ( r1_tarski @ X29 @ ( k1_setfam_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('22',plain,
    ( ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    r1_tarski @ ( k1_setfam_1 @ sk_B ) @ ( k1_setfam_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DPFy50j7yQ
% 0.12/0.35  % Computer   : n005.cluster.edu
% 0.12/0.35  % Model      : x86_64 x86_64
% 0.12/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.35  % Memory     : 8042.1875MB
% 0.12/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.35  % CPULimit   : 60
% 0.12/0.35  % DateTime   : Tue Dec  1 14:48:03 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.44/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.64  % Solved by: fo/fo7.sh
% 0.44/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.64  % done 481 iterations in 0.178s
% 0.44/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.64  % SZS output start Refutation
% 0.44/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.64  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.44/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.64  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.44/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.64  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.64  thf(t7_setfam_1, conjecture,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( r1_tarski @ A @ B ) =>
% 0.44/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.64         ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.44/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.64    (~( ![A:$i,B:$i]:
% 0.44/0.64        ( ( r1_tarski @ A @ B ) =>
% 0.44/0.64          ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.64            ( r1_tarski @ ( k1_setfam_1 @ B ) @ ( k1_setfam_1 @ A ) ) ) ) )),
% 0.44/0.64    inference('cnf.neg', [status(esa)], [t7_setfam_1])).
% 0.44/0.64  thf('0', plain,
% 0.44/0.64      (~ (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(t6_setfam_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.44/0.64       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.44/0.64  thf('1', plain,
% 0.44/0.64      (![X28 : $i, X29 : $i]:
% 0.44/0.64         (((X28) = (k1_xboole_0))
% 0.44/0.64          | (r2_hidden @ (sk_C @ X29 @ X28) @ X28)
% 0.44/0.64          | (r1_tarski @ X29 @ (k1_setfam_1 @ X28)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.44/0.64  thf(t48_xboole_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.64  thf('2', plain,
% 0.44/0.64      (![X14 : $i, X15 : $i]:
% 0.44/0.64         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.44/0.64           = (k3_xboole_0 @ X14 @ X15))),
% 0.44/0.64      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.64  thf(t79_xboole_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.44/0.64  thf('3', plain,
% 0.44/0.64      (![X21 : $i, X22 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X21 @ X22) @ X22)),
% 0.44/0.64      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.44/0.64  thf(symmetry_r1_xboole_0, axiom,
% 0.44/0.64    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.44/0.64  thf('4', plain,
% 0.44/0.64      (![X6 : $i, X7 : $i]:
% 0.44/0.64         ((r1_xboole_0 @ X6 @ X7) | ~ (r1_xboole_0 @ X7 @ X6))),
% 0.44/0.64      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.44/0.64  thf('5', plain,
% 0.44/0.64      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.64  thf('6', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf(t63_xboole_1, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.44/0.64       ( r1_xboole_0 @ A @ C ) ))).
% 0.44/0.64  thf('7', plain,
% 0.44/0.64      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.64         (~ (r1_tarski @ X16 @ X17)
% 0.44/0.64          | ~ (r1_xboole_0 @ X17 @ X18)
% 0.44/0.64          | (r1_xboole_0 @ X16 @ X18))),
% 0.44/0.64      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.44/0.64  thf('8', plain,
% 0.44/0.64      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B @ X0))),
% 0.44/0.64      inference('sup-', [status(thm)], ['6', '7'])).
% 0.44/0.64  thf('9', plain,
% 0.44/0.64      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['5', '8'])).
% 0.44/0.64  thf(t83_xboole_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.64  thf('10', plain,
% 0.44/0.64      (![X23 : $i, X24 : $i]:
% 0.44/0.64         (((k4_xboole_0 @ X23 @ X24) = (X23)) | ~ (r1_xboole_0 @ X23 @ X24))),
% 0.44/0.64      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.44/0.64  thf('11', plain,
% 0.44/0.64      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)) = (sk_A))),
% 0.44/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.44/0.64  thf('12', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.44/0.64      inference('sup+', [status(thm)], ['2', '11'])).
% 0.44/0.64  thf(d4_xboole_0, axiom,
% 0.44/0.64    (![A:$i,B:$i,C:$i]:
% 0.44/0.64     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.44/0.64       ( ![D:$i]:
% 0.44/0.64         ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.64           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.44/0.64  thf('13', plain,
% 0.44/0.64      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.64         (~ (r2_hidden @ X4 @ X3)
% 0.44/0.64          | (r2_hidden @ X4 @ X2)
% 0.44/0.64          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 0.44/0.64      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.44/0.64  thf('14', plain,
% 0.44/0.64      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.44/0.64         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.44/0.64      inference('simplify', [status(thm)], ['13'])).
% 0.44/0.64  thf('15', plain,
% 0.44/0.64      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['12', '14'])).
% 0.44/0.64  thf('16', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.44/0.64          | ((sk_A) = (k1_xboole_0))
% 0.44/0.64          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('sup-', [status(thm)], ['1', '15'])).
% 0.44/0.64  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('18', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.44/0.64          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.44/0.64      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.44/0.64  thf(t4_setfam_1, axiom,
% 0.44/0.64    (![A:$i,B:$i]:
% 0.44/0.64     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ ( k1_setfam_1 @ B ) @ A ) ))).
% 0.44/0.64  thf('19', plain,
% 0.44/0.64      (![X26 : $i, X27 : $i]:
% 0.44/0.64         ((r1_tarski @ (k1_setfam_1 @ X26) @ X27) | ~ (r2_hidden @ X27 @ X26))),
% 0.44/0.64      inference('cnf', [status(esa)], [t4_setfam_1])).
% 0.44/0.64  thf('20', plain,
% 0.44/0.64      (![X0 : $i]:
% 0.44/0.64         ((r1_tarski @ X0 @ (k1_setfam_1 @ sk_A))
% 0.44/0.64          | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (sk_C @ X0 @ sk_A)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.64  thf('21', plain,
% 0.44/0.64      (![X28 : $i, X29 : $i]:
% 0.44/0.64         (((X28) = (k1_xboole_0))
% 0.44/0.64          | ~ (r1_tarski @ X29 @ (sk_C @ X29 @ X28))
% 0.44/0.64          | (r1_tarski @ X29 @ (k1_setfam_1 @ X28)))),
% 0.44/0.64      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.44/0.64  thf('22', plain,
% 0.44/0.64      (((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.44/0.64        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))
% 0.44/0.64        | ((sk_A) = (k1_xboole_0)))),
% 0.44/0.64      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.64  thf('23', plain,
% 0.44/0.64      ((((sk_A) = (k1_xboole_0))
% 0.44/0.64        | (r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A)))),
% 0.44/0.64      inference('simplify', [status(thm)], ['22'])).
% 0.44/0.64  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.44/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.64  thf('25', plain, ((r1_tarski @ (k1_setfam_1 @ sk_B) @ (k1_setfam_1 @ sk_A))),
% 0.44/0.64      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.44/0.64  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.44/0.64  
% 0.44/0.64  % SZS output end Refutation
% 0.44/0.64  
% 0.44/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
