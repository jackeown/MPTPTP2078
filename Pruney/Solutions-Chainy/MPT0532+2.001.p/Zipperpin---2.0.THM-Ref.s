%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kfn25i4eoq

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:43 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   35 (  46 expanded)
%              Number of leaves         :   13 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  236 ( 386 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t132_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( r1_tarski @ B @ C )
             => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t132_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_B ) @ ( k8_relat_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k8_relat_1 @ X5 @ X4 )
        = ( k5_relat_1 @ X4 @ ( k6_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k8_relat_1 @ X5 @ X4 )
        = ( k5_relat_1 @ X4 @ ( k6_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t50_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ! [D: $i] :
                  ( ( v1_relat_1 @ D )
                 => ( ( ( r1_tarski @ A @ B )
                      & ( r1_tarski @ C @ D ) )
                   => ( r1_tarski @ ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( r1_tarski @ ( k5_relat_1 @ X8 @ X9 ) @ ( k5_relat_1 @ X6 @ X7 ) )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X8 @ X6 )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t50_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ X0 ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ sk_B @ X0 ) @ ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ sk_B @ X0 ) @ ( k5_relat_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ ( k8_relat_1 @ X0 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['1','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_B ) @ ( k8_relat_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kfn25i4eoq
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 19:15:46 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.32  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.18/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.45  % Solved by: fo/fo7.sh
% 0.18/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.45  % done 14 iterations in 0.015s
% 0.18/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.45  % SZS output start Refutation
% 0.18/0.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.18/0.45  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.18/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.45  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.18/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.45  thf(t132_relat_1, conjecture,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( v1_relat_1 @ B ) =>
% 0.18/0.45       ( ![C:$i]:
% 0.18/0.45         ( ( v1_relat_1 @ C ) =>
% 0.18/0.45           ( ( r1_tarski @ B @ C ) =>
% 0.18/0.45             ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.18/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.45    (~( ![A:$i,B:$i]:
% 0.18/0.45        ( ( v1_relat_1 @ B ) =>
% 0.18/0.45          ( ![C:$i]:
% 0.18/0.45            ( ( v1_relat_1 @ C ) =>
% 0.18/0.45              ( ( r1_tarski @ B @ C ) =>
% 0.18/0.45                ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ) )),
% 0.18/0.45    inference('cnf.neg', [status(esa)], [t132_relat_1])).
% 0.18/0.45  thf('0', plain,
% 0.18/0.45      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_B) @ (k8_relat_1 @ sk_A @ sk_C))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(t123_relat_1, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( v1_relat_1 @ B ) =>
% 0.18/0.45       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.18/0.45  thf('1', plain,
% 0.18/0.45      (![X4 : $i, X5 : $i]:
% 0.18/0.45         (((k8_relat_1 @ X5 @ X4) = (k5_relat_1 @ X4 @ (k6_relat_1 @ X5)))
% 0.18/0.45          | ~ (v1_relat_1 @ X4))),
% 0.18/0.45      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.18/0.45  thf('2', plain,
% 0.18/0.45      (![X4 : $i, X5 : $i]:
% 0.18/0.45         (((k8_relat_1 @ X5 @ X4) = (k5_relat_1 @ X4 @ (k6_relat_1 @ X5)))
% 0.18/0.45          | ~ (v1_relat_1 @ X4))),
% 0.18/0.45      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.18/0.45  thf('3', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(d10_xboole_0, axiom,
% 0.18/0.45    (![A:$i,B:$i]:
% 0.18/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.18/0.45  thf('4', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.18/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.18/0.45  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.18/0.45      inference('simplify', [status(thm)], ['4'])).
% 0.18/0.45  thf(t50_relat_1, axiom,
% 0.18/0.45    (![A:$i]:
% 0.18/0.45     ( ( v1_relat_1 @ A ) =>
% 0.18/0.45       ( ![B:$i]:
% 0.18/0.45         ( ( v1_relat_1 @ B ) =>
% 0.18/0.45           ( ![C:$i]:
% 0.18/0.45             ( ( v1_relat_1 @ C ) =>
% 0.18/0.45               ( ![D:$i]:
% 0.18/0.45                 ( ( v1_relat_1 @ D ) =>
% 0.18/0.45                   ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.18/0.45                     ( r1_tarski @
% 0.18/0.45                       ( k5_relat_1 @ A @ C ) @ ( k5_relat_1 @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.18/0.45  thf('6', plain,
% 0.18/0.45      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.18/0.45         (~ (v1_relat_1 @ X6)
% 0.18/0.45          | ~ (v1_relat_1 @ X7)
% 0.18/0.45          | (r1_tarski @ (k5_relat_1 @ X8 @ X9) @ (k5_relat_1 @ X6 @ X7))
% 0.18/0.45          | ~ (r1_tarski @ X9 @ X7)
% 0.18/0.45          | ~ (r1_tarski @ X8 @ X6)
% 0.18/0.45          | ~ (v1_relat_1 @ X9)
% 0.18/0.45          | ~ (v1_relat_1 @ X8))),
% 0.18/0.45      inference('cnf', [status(esa)], [t50_relat_1])).
% 0.18/0.45  thf('7', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.45         (~ (v1_relat_1 @ X1)
% 0.18/0.45          | ~ (v1_relat_1 @ X0)
% 0.18/0.45          | ~ (r1_tarski @ X1 @ X2)
% 0.18/0.45          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ (k5_relat_1 @ X2 @ X0))
% 0.18/0.45          | ~ (v1_relat_1 @ X0)
% 0.18/0.45          | ~ (v1_relat_1 @ X2))),
% 0.18/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.18/0.45  thf('8', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.45         (~ (v1_relat_1 @ X2)
% 0.18/0.45          | (r1_tarski @ (k5_relat_1 @ X1 @ X0) @ (k5_relat_1 @ X2 @ X0))
% 0.18/0.45          | ~ (r1_tarski @ X1 @ X2)
% 0.18/0.45          | ~ (v1_relat_1 @ X0)
% 0.18/0.45          | ~ (v1_relat_1 @ X1))),
% 0.18/0.45      inference('simplify', [status(thm)], ['7'])).
% 0.18/0.45  thf('9', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         (~ (v1_relat_1 @ sk_B)
% 0.18/0.45          | ~ (v1_relat_1 @ X0)
% 0.18/0.45          | (r1_tarski @ (k5_relat_1 @ sk_B @ X0) @ (k5_relat_1 @ sk_C @ X0))
% 0.18/0.45          | ~ (v1_relat_1 @ sk_C))),
% 0.18/0.45      inference('sup-', [status(thm)], ['3', '8'])).
% 0.18/0.45  thf('10', plain, ((v1_relat_1 @ sk_B)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('12', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         (~ (v1_relat_1 @ X0)
% 0.18/0.45          | (r1_tarski @ (k5_relat_1 @ sk_B @ X0) @ (k5_relat_1 @ sk_C @ X0)))),
% 0.18/0.45      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.18/0.45  thf('13', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ 
% 0.18/0.45           (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))
% 0.18/0.45          | ~ (v1_relat_1 @ sk_B)
% 0.18/0.45          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.18/0.45      inference('sup+', [status(thm)], ['2', '12'])).
% 0.18/0.45  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.18/0.45  thf('15', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.18/0.45      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.18/0.45  thf('16', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         (r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ 
% 0.18/0.45          (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))),
% 0.18/0.45      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.18/0.45  thf('17', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ (k8_relat_1 @ X0 @ sk_C))
% 0.18/0.45          | ~ (v1_relat_1 @ sk_C))),
% 0.18/0.45      inference('sup+', [status(thm)], ['1', '16'])).
% 0.18/0.45  thf('18', plain, ((v1_relat_1 @ sk_C)),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('19', plain,
% 0.18/0.45      (![X0 : $i]:
% 0.18/0.45         (r1_tarski @ (k8_relat_1 @ X0 @ sk_B) @ (k8_relat_1 @ X0 @ sk_C))),
% 0.18/0.45      inference('demod', [status(thm)], ['17', '18'])).
% 0.18/0.45  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.18/0.45  
% 0.18/0.45  % SZS output end Refutation
% 0.18/0.45  
% 0.18/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
