%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OgsrraCRZo

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:50 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   38 (  39 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  269 ( 277 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t86_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t86_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ sk_B @ sk_A ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X9 @ X10 )
      | ( r1_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t107_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r1_tarski @ X0 @ ( k5_xboole_0 @ X1 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X3 ) )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t107_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X19 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t96_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ ( k5_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t96_xboole_1])).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X19 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ( r1_tarski @ ( k2_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X2 ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.17  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OgsrraCRZo
% 0.18/0.38  % Computer   : n025.cluster.edu
% 0.18/0.38  % Model      : x86_64 x86_64
% 0.18/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.18/0.38  % Memory     : 8042.1875MB
% 0.18/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.38  % CPULimit   : 60
% 0.18/0.38  % DateTime   : Tue Dec  1 14:37:36 EST 2020
% 0.18/0.38  % CPUTime    : 
% 0.18/0.38  % Running portfolio for 600 s
% 0.18/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.38  % Number of cores: 8
% 0.18/0.39  % Python version: Python 3.6.8
% 0.18/0.39  % Running in FO mode
% 0.58/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.81  % Solved by: fo/fo7.sh
% 0.58/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.81  % done 249 iterations in 0.316s
% 0.58/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.81  % SZS output start Refutation
% 0.58/0.81  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.81  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.81  thf(t86_zfmisc_1, conjecture,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( r1_tarski @
% 0.58/0.81       ( k2_xboole_0 @
% 0.58/0.81         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 0.58/0.81         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 0.58/0.81       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 0.58/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.81    (~( ![A:$i,B:$i]:
% 0.58/0.81        ( r1_tarski @
% 0.58/0.81          ( k2_xboole_0 @
% 0.58/0.81            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 0.58/0.81            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 0.58/0.81          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 0.58/0.81    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 0.58/0.81  thf('0', plain,
% 0.58/0.81      (~ (r1_tarski @ 
% 0.58/0.81          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 0.58/0.81           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 0.58/0.81          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.58/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.81  thf(t36_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.58/0.81  thf('1', plain,
% 0.58/0.81      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 0.58/0.81      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.58/0.81  thf(t10_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.58/0.81  thf('2', plain,
% 0.58/0.81      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.81         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ X4 @ (k2_xboole_0 @ X6 @ X5)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.58/0.81  thf('3', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X2 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.81  thf(t79_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.58/0.81  thf('4', plain,
% 0.58/0.81      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.58/0.81      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.58/0.81  thf(t74_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.58/0.81          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.58/0.81  thf('5', plain,
% 0.58/0.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.81         (~ (r1_xboole_0 @ X9 @ X10)
% 0.58/0.81          | (r1_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.58/0.81  thf('6', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X2))),
% 0.58/0.81      inference('sup-', [status(thm)], ['4', '5'])).
% 0.58/0.81  thf(t107_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.58/0.81       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 0.58/0.81         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.58/0.81  thf('7', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.58/0.81         ((r1_tarski @ X0 @ (k5_xboole_0 @ X1 @ X3))
% 0.58/0.81          | ~ (r1_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X3))
% 0.58/0.81          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X3)))),
% 0.58/0.81      inference('cnf', [status(esa)], [t107_xboole_1])).
% 0.58/0.81  thf('8', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         (~ (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))
% 0.58/0.81          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.58/0.81  thf('9', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0))),
% 0.58/0.81      inference('sup-', [status(thm)], ['3', '8'])).
% 0.58/0.81  thf(t79_zfmisc_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( ( r1_tarski @ A @ B ) =>
% 0.58/0.81       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.58/0.81  thf('10', plain,
% 0.58/0.81      (![X19 : $i, X20 : $i]:
% 0.58/0.81         ((r1_tarski @ (k1_zfmisc_1 @ X19) @ (k1_zfmisc_1 @ X20))
% 0.58/0.81          | ~ (r1_tarski @ X19 @ X20))),
% 0.58/0.81      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.58/0.81  thf('11', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1)) @ 
% 0.58/0.81          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['9', '10'])).
% 0.58/0.81  thf(t96_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i]:
% 0.58/0.81     ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 0.58/0.81  thf('12', plain,
% 0.58/0.81      (![X17 : $i, X18 : $i]:
% 0.58/0.81         (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ (k5_xboole_0 @ X17 @ X18))),
% 0.58/0.81      inference('cnf', [status(esa)], [t96_xboole_1])).
% 0.58/0.81  thf('13', plain,
% 0.58/0.81      (![X19 : $i, X20 : $i]:
% 0.58/0.81         ((r1_tarski @ (k1_zfmisc_1 @ X19) @ (k1_zfmisc_1 @ X20))
% 0.58/0.81          | ~ (r1_tarski @ X19 @ X20))),
% 0.58/0.81      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.58/0.81  thf('14', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (r1_tarski @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.58/0.81          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['12', '13'])).
% 0.58/0.81  thf(t8_xboole_1, axiom,
% 0.58/0.81    (![A:$i,B:$i,C:$i]:
% 0.58/0.81     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.58/0.81       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.58/0.81  thf('15', plain,
% 0.58/0.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.81         (~ (r1_tarski @ X14 @ X15)
% 0.58/0.81          | ~ (r1_tarski @ X16 @ X15)
% 0.58/0.81          | (r1_tarski @ (k2_xboole_0 @ X14 @ X16) @ X15))),
% 0.58/0.81      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.58/0.81  thf('16', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.81         ((r1_tarski @ 
% 0.58/0.81           (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ X2) @ 
% 0.58/0.81           (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))
% 0.58/0.81          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0))))),
% 0.58/0.81      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.81  thf('17', plain,
% 0.58/0.81      (![X0 : $i, X1 : $i]:
% 0.58/0.81         (r1_tarski @ 
% 0.58/0.81          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 0.58/0.81           (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 0.58/0.81          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.58/0.81      inference('sup-', [status(thm)], ['11', '16'])).
% 0.58/0.81  thf('18', plain, ($false), inference('demod', [status(thm)], ['0', '17'])).
% 0.58/0.81  
% 0.58/0.81  % SZS output end Refutation
% 0.58/0.81  
% 0.58/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
