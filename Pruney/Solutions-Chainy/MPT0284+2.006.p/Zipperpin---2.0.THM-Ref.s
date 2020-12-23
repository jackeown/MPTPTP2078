%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3n50f2c3BB

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:48 EST 2020

% Result     : Theorem 17.80s
% Output     : Refutation 17.80s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  198 ( 211 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X2 @ X3 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X2 @ X3 ) @ ( k4_xboole_0 @ X3 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X19 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X19 ) @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ( r1_tarski @ ( k2_xboole_0 @ X14 @ X16 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k1_zfmisc_1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','12'])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['0','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3n50f2c3BB
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:44:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 17.80/18.05  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 17.80/18.05  % Solved by: fo/fo7.sh
% 17.80/18.05  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.80/18.05  % done 11012 iterations in 17.608s
% 17.80/18.05  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 17.80/18.05  % SZS output start Refutation
% 17.80/18.05  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 17.80/18.05  thf(sk_A_type, type, sk_A: $i).
% 17.80/18.05  thf(sk_B_type, type, sk_B: $i).
% 17.80/18.05  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 17.80/18.05  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 17.80/18.05  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.80/18.05  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 17.80/18.05  thf(t86_zfmisc_1, conjecture,
% 17.80/18.05    (![A:$i,B:$i]:
% 17.80/18.05     ( r1_tarski @
% 17.80/18.05       ( k2_xboole_0 @
% 17.80/18.05         ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 17.80/18.05         ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 17.80/18.05       ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ))).
% 17.80/18.05  thf(zf_stmt_0, negated_conjecture,
% 17.80/18.05    (~( ![A:$i,B:$i]:
% 17.80/18.05        ( r1_tarski @
% 17.80/18.05          ( k2_xboole_0 @
% 17.80/18.05            ( k1_zfmisc_1 @ ( k4_xboole_0 @ A @ B ) ) @ 
% 17.80/18.05            ( k1_zfmisc_1 @ ( k4_xboole_0 @ B @ A ) ) ) @ 
% 17.80/18.05          ( k1_zfmisc_1 @ ( k5_xboole_0 @ A @ B ) ) ) )),
% 17.80/18.05    inference('cnf.neg', [status(esa)], [t86_zfmisc_1])).
% 17.80/18.05  thf('0', plain,
% 17.80/18.05      (~ (r1_tarski @ 
% 17.80/18.05          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ sk_A @ sk_B)) @ 
% 17.80/18.05           (k1_zfmisc_1 @ (k4_xboole_0 @ sk_B @ sk_A))) @ 
% 17.80/18.05          (k1_zfmisc_1 @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 17.80/18.05      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.80/18.05  thf(d6_xboole_0, axiom,
% 17.80/18.05    (![A:$i,B:$i]:
% 17.80/18.05     ( ( k5_xboole_0 @ A @ B ) =
% 17.80/18.05       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 17.80/18.05  thf('1', plain,
% 17.80/18.05      (![X2 : $i, X3 : $i]:
% 17.80/18.05         ((k5_xboole_0 @ X2 @ X3)
% 17.80/18.05           = (k2_xboole_0 @ (k4_xboole_0 @ X2 @ X3) @ (k4_xboole_0 @ X3 @ X2)))),
% 17.80/18.05      inference('cnf', [status(esa)], [d6_xboole_0])).
% 17.80/18.05  thf(commutativity_k2_xboole_0, axiom,
% 17.80/18.05    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 17.80/18.05  thf('2', plain,
% 17.80/18.05      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 17.80/18.05      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 17.80/18.05  thf(t7_xboole_1, axiom,
% 17.80/18.05    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 17.80/18.05  thf('3', plain,
% 17.80/18.05      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 17.80/18.05      inference('cnf', [status(esa)], [t7_xboole_1])).
% 17.80/18.05  thf('4', plain,
% 17.80/18.05      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 17.80/18.05      inference('sup+', [status(thm)], ['2', '3'])).
% 17.80/18.05  thf(t79_zfmisc_1, axiom,
% 17.80/18.05    (![A:$i,B:$i]:
% 17.80/18.05     ( ( r1_tarski @ A @ B ) =>
% 17.80/18.05       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 17.80/18.05  thf('5', plain,
% 17.80/18.05      (![X19 : $i, X20 : $i]:
% 17.80/18.05         ((r1_tarski @ (k1_zfmisc_1 @ X19) @ (k1_zfmisc_1 @ X20))
% 17.80/18.05          | ~ (r1_tarski @ X19 @ X20))),
% 17.80/18.05      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 17.80/18.05  thf('6', plain,
% 17.80/18.05      (![X0 : $i, X1 : $i]:
% 17.80/18.05         (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 17.80/18.05          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 17.80/18.05      inference('sup-', [status(thm)], ['4', '5'])).
% 17.80/18.05  thf('7', plain,
% 17.80/18.05      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 17.80/18.05      inference('cnf', [status(esa)], [t7_xboole_1])).
% 17.80/18.05  thf('8', plain,
% 17.80/18.05      (![X19 : $i, X20 : $i]:
% 17.80/18.05         ((r1_tarski @ (k1_zfmisc_1 @ X19) @ (k1_zfmisc_1 @ X20))
% 17.80/18.05          | ~ (r1_tarski @ X19 @ X20))),
% 17.80/18.05      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 17.80/18.05  thf('9', plain,
% 17.80/18.05      (![X0 : $i, X1 : $i]:
% 17.80/18.05         (r1_tarski @ (k1_zfmisc_1 @ X1) @ 
% 17.80/18.05          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 17.80/18.05      inference('sup-', [status(thm)], ['7', '8'])).
% 17.80/18.05  thf(t8_xboole_1, axiom,
% 17.80/18.05    (![A:$i,B:$i,C:$i]:
% 17.80/18.05     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 17.80/18.05       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 17.80/18.05  thf('10', plain,
% 17.80/18.05      (![X14 : $i, X15 : $i, X16 : $i]:
% 17.80/18.05         (~ (r1_tarski @ X14 @ X15)
% 17.80/18.05          | ~ (r1_tarski @ X16 @ X15)
% 17.80/18.05          | (r1_tarski @ (k2_xboole_0 @ X14 @ X16) @ X15))),
% 17.80/18.05      inference('cnf', [status(esa)], [t8_xboole_1])).
% 17.80/18.05  thf('11', plain,
% 17.80/18.05      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.80/18.05         ((r1_tarski @ (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ X2) @ 
% 17.80/18.05           (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 17.80/18.05          | ~ (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 17.80/18.05      inference('sup-', [status(thm)], ['9', '10'])).
% 17.80/18.05  thf('12', plain,
% 17.80/18.05      (![X0 : $i, X1 : $i]:
% 17.80/18.05         (r1_tarski @ 
% 17.80/18.05          (k2_xboole_0 @ (k1_zfmisc_1 @ X1) @ (k1_zfmisc_1 @ X0)) @ 
% 17.80/18.05          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 17.80/18.05      inference('sup-', [status(thm)], ['6', '11'])).
% 17.80/18.05  thf('13', plain,
% 17.80/18.05      (![X0 : $i, X1 : $i]:
% 17.80/18.05         (r1_tarski @ 
% 17.80/18.05          (k2_xboole_0 @ (k1_zfmisc_1 @ (k4_xboole_0 @ X1 @ X0)) @ 
% 17.80/18.05           (k1_zfmisc_1 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 17.80/18.05          (k1_zfmisc_1 @ (k5_xboole_0 @ X1 @ X0)))),
% 17.80/18.05      inference('sup+', [status(thm)], ['1', '12'])).
% 17.80/18.05  thf('14', plain, ($false), inference('demod', [status(thm)], ['0', '13'])).
% 17.80/18.05  
% 17.80/18.05  % SZS output end Refutation
% 17.80/18.05  
% 17.87/18.06  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
