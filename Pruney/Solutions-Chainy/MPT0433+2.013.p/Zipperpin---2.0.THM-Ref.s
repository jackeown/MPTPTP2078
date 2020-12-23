%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u8UkZIRupr

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:39 EST 2020

% Result     : Theorem 2.95s
% Output     : Refutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   49 (  80 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  322 ( 587 expanded)
%              Number of equality atoms :   11 (  22 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = X1 ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( ( k1_relat_1 @ ( k2_xboole_0 @ X28 @ X27 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X28 ) @ ( k1_relat_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t13_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ X11 @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X22: $i,X24: $i] :
      ( ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X24 ) )
      | ~ ( r1_tarski @ X22 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_relat_1 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['9','16'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X4 @ X6 )
      | ( r1_tarski @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t14_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t14_relat_1])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['24','25','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.u8UkZIRupr
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:52:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 2.95/3.13  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.95/3.13  % Solved by: fo/fo7.sh
% 2.95/3.13  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.95/3.13  % done 4336 iterations in 2.684s
% 2.95/3.13  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.95/3.13  % SZS output start Refutation
% 2.95/3.13  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.95/3.13  thf(sk_A_type, type, sk_A: $i).
% 2.95/3.13  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.95/3.13  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.95/3.13  thf(sk_B_type, type, sk_B: $i).
% 2.95/3.13  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.95/3.13  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.95/3.13  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.95/3.13  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.95/3.13  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.95/3.13  thf(commutativity_k3_xboole_0, axiom,
% 2.95/3.13    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.95/3.13  thf('0', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.95/3.13      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.95/3.13  thf(t48_xboole_1, axiom,
% 2.95/3.13    (![A:$i,B:$i]:
% 2.95/3.13     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.95/3.13  thf('1', plain,
% 2.95/3.13      (![X9 : $i, X10 : $i]:
% 2.95/3.13         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 2.95/3.13           = (k3_xboole_0 @ X9 @ X10))),
% 2.95/3.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.95/3.13  thf(t36_xboole_1, axiom,
% 2.95/3.13    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 2.95/3.13  thf('2', plain,
% 2.95/3.13      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 2.95/3.13      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.95/3.13  thf(t12_xboole_1, axiom,
% 2.95/3.13    (![A:$i,B:$i]:
% 2.95/3.13     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.95/3.13  thf('3', plain,
% 2.95/3.13      (![X2 : $i, X3 : $i]:
% 2.95/3.13         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.95/3.13      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.95/3.13  thf('4', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]:
% 2.95/3.13         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.95/3.13      inference('sup-', [status(thm)], ['2', '3'])).
% 2.95/3.13  thf('5', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]:
% 2.95/3.13         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (X1))),
% 2.95/3.13      inference('sup+', [status(thm)], ['1', '4'])).
% 2.95/3.13  thf(t13_relat_1, axiom,
% 2.95/3.13    (![A:$i]:
% 2.95/3.13     ( ( v1_relat_1 @ A ) =>
% 2.95/3.13       ( ![B:$i]:
% 2.95/3.13         ( ( v1_relat_1 @ B ) =>
% 2.95/3.13           ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 2.95/3.13             ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 2.95/3.13  thf('6', plain,
% 2.95/3.13      (![X27 : $i, X28 : $i]:
% 2.95/3.13         (~ (v1_relat_1 @ X27)
% 2.95/3.13          | ((k1_relat_1 @ (k2_xboole_0 @ X28 @ X27))
% 2.95/3.13              = (k2_xboole_0 @ (k1_relat_1 @ X28) @ (k1_relat_1 @ X27)))
% 2.95/3.13          | ~ (v1_relat_1 @ X28))),
% 2.95/3.13      inference('cnf', [status(esa)], [t13_relat_1])).
% 2.95/3.13  thf(t7_xboole_1, axiom,
% 2.95/3.13    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.95/3.13  thf('7', plain,
% 2.95/3.13      (![X11 : $i, X12 : $i]: (r1_tarski @ X11 @ (k2_xboole_0 @ X11 @ X12))),
% 2.95/3.13      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.95/3.13  thf('8', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]:
% 2.95/3.13         ((r1_tarski @ (k1_relat_1 @ X1) @ 
% 2.95/3.13           (k1_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.95/3.13          | ~ (v1_relat_1 @ X1)
% 2.95/3.13          | ~ (v1_relat_1 @ X0))),
% 2.95/3.13      inference('sup+', [status(thm)], ['6', '7'])).
% 2.95/3.13  thf('9', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]:
% 2.95/3.13         ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.95/3.13           (k1_relat_1 @ X0))
% 2.95/3.13          | ~ (v1_relat_1 @ X0)
% 2.95/3.13          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.95/3.13      inference('sup+', [status(thm)], ['5', '8'])).
% 2.95/3.13  thf('10', plain,
% 2.95/3.13      (![X9 : $i, X10 : $i]:
% 2.95/3.13         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 2.95/3.13           = (k3_xboole_0 @ X9 @ X10))),
% 2.95/3.13      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.95/3.13  thf('11', plain,
% 2.95/3.13      (![X7 : $i, X8 : $i]: (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X7)),
% 2.95/3.13      inference('cnf', [status(esa)], [t36_xboole_1])).
% 2.95/3.13  thf('12', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 2.95/3.13      inference('sup+', [status(thm)], ['10', '11'])).
% 2.95/3.13  thf(t3_subset, axiom,
% 2.95/3.13    (![A:$i,B:$i]:
% 2.95/3.13     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.95/3.13  thf('13', plain,
% 2.95/3.13      (![X22 : $i, X24 : $i]:
% 2.95/3.13         ((m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X24)) | ~ (r1_tarski @ X22 @ X24))),
% 2.95/3.13      inference('cnf', [status(esa)], [t3_subset])).
% 2.95/3.13  thf('14', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]:
% 2.95/3.13         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.95/3.13      inference('sup-', [status(thm)], ['12', '13'])).
% 2.95/3.13  thf(cc2_relat_1, axiom,
% 2.95/3.13    (![A:$i]:
% 2.95/3.13     ( ( v1_relat_1 @ A ) =>
% 2.95/3.13       ( ![B:$i]:
% 2.95/3.13         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.95/3.13  thf('15', plain,
% 2.95/3.13      (![X25 : $i, X26 : $i]:
% 2.95/3.13         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 2.95/3.13          | (v1_relat_1 @ X25)
% 2.95/3.13          | ~ (v1_relat_1 @ X26))),
% 2.95/3.13      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.95/3.13  thf('16', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]:
% 2.95/3.13         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.95/3.13      inference('sup-', [status(thm)], ['14', '15'])).
% 2.95/3.13  thf('17', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]:
% 2.95/3.13         (~ (v1_relat_1 @ X0)
% 2.95/3.13          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.95/3.13             (k1_relat_1 @ X0)))),
% 2.95/3.13      inference('clc', [status(thm)], ['9', '16'])).
% 2.95/3.13  thf('18', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]:
% 2.95/3.13         ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.95/3.13           (k1_relat_1 @ X0))
% 2.95/3.13          | ~ (v1_relat_1 @ X0))),
% 2.95/3.13      inference('sup+', [status(thm)], ['0', '17'])).
% 2.95/3.13  thf('19', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]:
% 2.95/3.13         (~ (v1_relat_1 @ X0)
% 2.95/3.13          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.95/3.13             (k1_relat_1 @ X0)))),
% 2.95/3.13      inference('clc', [status(thm)], ['9', '16'])).
% 2.95/3.13  thf(t19_xboole_1, axiom,
% 2.95/3.13    (![A:$i,B:$i,C:$i]:
% 2.95/3.13     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 2.95/3.13       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.95/3.13  thf('20', plain,
% 2.95/3.13      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.95/3.13         (~ (r1_tarski @ X4 @ X5)
% 2.95/3.13          | ~ (r1_tarski @ X4 @ X6)
% 2.95/3.13          | (r1_tarski @ X4 @ (k3_xboole_0 @ X5 @ X6)))),
% 2.95/3.13      inference('cnf', [status(esa)], [t19_xboole_1])).
% 2.95/3.13  thf('21', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.95/3.13         (~ (v1_relat_1 @ X0)
% 2.95/3.13          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.95/3.13             (k3_xboole_0 @ (k1_relat_1 @ X0) @ X2))
% 2.95/3.13          | ~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 2.95/3.13      inference('sup-', [status(thm)], ['19', '20'])).
% 2.95/3.13  thf('22', plain,
% 2.95/3.13      (![X0 : $i, X1 : $i]:
% 2.95/3.13         (~ (v1_relat_1 @ X0)
% 2.95/3.13          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.95/3.13             (k3_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 2.95/3.13          | ~ (v1_relat_1 @ X1))),
% 2.95/3.13      inference('sup-', [status(thm)], ['18', '21'])).
% 2.95/3.13  thf(t14_relat_1, conjecture,
% 2.95/3.13    (![A:$i]:
% 2.95/3.13     ( ( v1_relat_1 @ A ) =>
% 2.95/3.13       ( ![B:$i]:
% 2.95/3.13         ( ( v1_relat_1 @ B ) =>
% 2.95/3.13           ( r1_tarski @
% 2.95/3.13             ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 2.95/3.13             ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 2.95/3.13  thf(zf_stmt_0, negated_conjecture,
% 2.95/3.13    (~( ![A:$i]:
% 2.95/3.13        ( ( v1_relat_1 @ A ) =>
% 2.95/3.13          ( ![B:$i]:
% 2.95/3.13            ( ( v1_relat_1 @ B ) =>
% 2.95/3.13              ( r1_tarski @
% 2.95/3.13                ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 2.95/3.13                ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )),
% 2.95/3.13    inference('cnf.neg', [status(esa)], [t14_relat_1])).
% 2.95/3.13  thf('23', plain,
% 2.95/3.13      (~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 2.95/3.13          (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 2.95/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.13  thf('24', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 2.95/3.13      inference('sup-', [status(thm)], ['22', '23'])).
% 2.95/3.13  thf('25', plain, ((v1_relat_1 @ sk_A)),
% 2.95/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.13  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 2.95/3.13      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.95/3.13  thf('27', plain, ($false),
% 2.95/3.13      inference('demod', [status(thm)], ['24', '25', '26'])).
% 2.95/3.13  
% 2.95/3.13  % SZS output end Refutation
% 2.95/3.13  
% 2.95/3.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
