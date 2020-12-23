%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SkX3WYYj0k

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:20 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   34 (  43 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :  233 ( 340 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t178_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ( r1_tarski @ X5 @ ( sk_D @ X5 @ X4 @ X3 ) )
      | ( X4
        = ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ~ ( r1_tarski @ X4 @ ( sk_D @ X5 @ X4 @ X3 ) )
      | ( X4
        = ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('7',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k10_relat_1 @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X8 @ X9 ) @ ( k10_relat_1 @ X8 @ X10 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','14'])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['17','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SkX3WYYj0k
% 0.15/0.37  % Computer   : n016.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 20:45:34 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 26 iterations in 0.024s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.23/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.51  thf(d10_xboole_0, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.23/0.51      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.23/0.51  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.23/0.51  thf(t178_relat_1, conjecture,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ C ) =>
% 0.23/0.51       ( ( r1_tarski @ A @ B ) =>
% 0.23/0.51         ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.51        ( ( v1_relat_1 @ C ) =>
% 0.23/0.51          ( ( r1_tarski @ A @ B ) =>
% 0.23/0.51            ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t178_relat_1])).
% 0.23/0.51  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(t14_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.23/0.51         ( ![D:$i]:
% 0.23/0.51           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.23/0.51             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.23/0.51       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.23/0.51  thf('3', plain,
% 0.23/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.51         (~ (r1_tarski @ X3 @ X4)
% 0.23/0.51          | ~ (r1_tarski @ X5 @ X4)
% 0.23/0.51          | (r1_tarski @ X5 @ (sk_D @ X5 @ X4 @ X3))
% 0.23/0.51          | ((X4) = (k2_xboole_0 @ X3 @ X5)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((sk_B) = (k2_xboole_0 @ sk_A @ X0))
% 0.23/0.51          | (r1_tarski @ X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.23/0.51          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      (((r1_tarski @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A))
% 0.23/0.51        | ((sk_B) = (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '4'])).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.23/0.51         (~ (r1_tarski @ X3 @ X4)
% 0.23/0.51          | ~ (r1_tarski @ X5 @ X4)
% 0.23/0.51          | ~ (r1_tarski @ X4 @ (sk_D @ X5 @ X4 @ X3))
% 0.23/0.51          | ((X4) = (k2_xboole_0 @ X3 @ X5)))),
% 0.23/0.51      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      ((((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))
% 0.23/0.51        | ((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))
% 0.23/0.51        | ~ (r1_tarski @ sk_B @ sk_B)
% 0.23/0.51        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.23/0.51      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.51  thf('8', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.23/0.51      inference('simplify', [status(thm)], ['0'])).
% 0.23/0.51  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      ((((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))
% 0.23/0.51        | ((sk_B) = (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.23/0.51      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.23/0.51  thf('11', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.23/0.51      inference('simplify', [status(thm)], ['10'])).
% 0.23/0.51  thf(t175_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ C ) =>
% 0.23/0.51       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.23/0.51         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.23/0.51  thf('12', plain,
% 0.23/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.23/0.51         (((k10_relat_1 @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 0.23/0.51            = (k2_xboole_0 @ (k10_relat_1 @ X8 @ X9) @ (k10_relat_1 @ X8 @ X10)))
% 0.23/0.51          | ~ (v1_relat_1 @ X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.23/0.51  thf(t7_xboole_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      (![X6 : $i, X7 : $i]: (r1_tarski @ X6 @ (k2_xboole_0 @ X6 @ X7))),
% 0.23/0.51      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.51         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.23/0.51           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.23/0.51          | ~ (v1_relat_1 @ X2))),
% 0.23/0.51      inference('sup+', [status(thm)], ['12', '13'])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B))
% 0.23/0.51          | ~ (v1_relat_1 @ X0))),
% 0.23/0.51      inference('sup+', [status(thm)], ['11', '14'])).
% 0.23/0.51  thf('16', plain,
% 0.23/0.51      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('17', plain, (~ (v1_relat_1 @ sk_C)),
% 0.23/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.23/0.51  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('19', plain, ($false), inference('demod', [status(thm)], ['17', '18'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
