%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PpXV2Zdk24

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:39 EST 2020

% Result     : Theorem 2.34s
% Output     : Refutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   43 (  67 expanded)
%              Number of leaves         :   18 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  283 ( 491 expanded)
%              Number of equality atoms :    7 (  12 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ( ( k1_relat_1 @ ( k2_xboole_0 @ X26 @ X25 ) )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X26 ) @ ( k1_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t13_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X4 @ X5 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) )
      | ( v1_relat_1 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','12'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ X8 )
      | ( r1_tarski @ X6 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

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

thf('19',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['20','21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PpXV2Zdk24
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:25:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.34/2.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.34/2.56  % Solved by: fo/fo7.sh
% 2.34/2.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.34/2.56  % done 3744 iterations in 2.109s
% 2.34/2.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.34/2.56  % SZS output start Refutation
% 2.34/2.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.34/2.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.34/2.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.34/2.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.34/2.56  thf(sk_B_type, type, sk_B: $i).
% 2.34/2.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.34/2.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.34/2.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.34/2.56  thf(sk_A_type, type, sk_A: $i).
% 2.34/2.56  thf(commutativity_k3_xboole_0, axiom,
% 2.34/2.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.34/2.56  thf('0', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.34/2.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.34/2.56  thf(t17_xboole_1, axiom,
% 2.34/2.56    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.34/2.56  thf('1', plain,
% 2.34/2.56      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 2.34/2.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.34/2.56  thf(t12_xboole_1, axiom,
% 2.34/2.56    (![A:$i,B:$i]:
% 2.34/2.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.34/2.56  thf('2', plain,
% 2.34/2.56      (![X2 : $i, X3 : $i]:
% 2.34/2.56         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 2.34/2.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.34/2.56  thf('3', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i]:
% 2.34/2.56         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.34/2.56      inference('sup-', [status(thm)], ['1', '2'])).
% 2.34/2.56  thf(t13_relat_1, axiom,
% 2.34/2.56    (![A:$i]:
% 2.34/2.56     ( ( v1_relat_1 @ A ) =>
% 2.34/2.56       ( ![B:$i]:
% 2.34/2.56         ( ( v1_relat_1 @ B ) =>
% 2.34/2.56           ( ( k1_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 2.34/2.56             ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 2.34/2.56  thf('4', plain,
% 2.34/2.56      (![X25 : $i, X26 : $i]:
% 2.34/2.56         (~ (v1_relat_1 @ X25)
% 2.34/2.56          | ((k1_relat_1 @ (k2_xboole_0 @ X26 @ X25))
% 2.34/2.56              = (k2_xboole_0 @ (k1_relat_1 @ X26) @ (k1_relat_1 @ X25)))
% 2.34/2.56          | ~ (v1_relat_1 @ X26))),
% 2.34/2.56      inference('cnf', [status(esa)], [t13_relat_1])).
% 2.34/2.56  thf(t7_xboole_1, axiom,
% 2.34/2.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 2.34/2.56  thf('5', plain,
% 2.34/2.56      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 2.34/2.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 2.34/2.56  thf('6', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i]:
% 2.34/2.56         ((r1_tarski @ (k1_relat_1 @ X1) @ 
% 2.34/2.56           (k1_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 2.34/2.56          | ~ (v1_relat_1 @ X1)
% 2.34/2.56          | ~ (v1_relat_1 @ X0))),
% 2.34/2.56      inference('sup+', [status(thm)], ['4', '5'])).
% 2.34/2.56  thf('7', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i]:
% 2.34/2.56         ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.34/2.56           (k1_relat_1 @ X0))
% 2.34/2.56          | ~ (v1_relat_1 @ X0)
% 2.34/2.56          | ~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.34/2.56      inference('sup+', [status(thm)], ['3', '6'])).
% 2.34/2.56  thf('8', plain,
% 2.34/2.56      (![X4 : $i, X5 : $i]: (r1_tarski @ (k3_xboole_0 @ X4 @ X5) @ X4)),
% 2.34/2.56      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.34/2.56  thf(t3_subset, axiom,
% 2.34/2.56    (![A:$i,B:$i]:
% 2.34/2.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.34/2.56  thf('9', plain,
% 2.34/2.56      (![X20 : $i, X22 : $i]:
% 2.34/2.56         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 2.34/2.56      inference('cnf', [status(esa)], [t3_subset])).
% 2.34/2.56  thf('10', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i]:
% 2.34/2.56         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 2.34/2.56      inference('sup-', [status(thm)], ['8', '9'])).
% 2.34/2.56  thf(cc2_relat_1, axiom,
% 2.34/2.56    (![A:$i]:
% 2.34/2.56     ( ( v1_relat_1 @ A ) =>
% 2.34/2.56       ( ![B:$i]:
% 2.34/2.56         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.34/2.56  thf('11', plain,
% 2.34/2.56      (![X23 : $i, X24 : $i]:
% 2.34/2.56         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24))
% 2.34/2.56          | (v1_relat_1 @ X23)
% 2.34/2.56          | ~ (v1_relat_1 @ X24))),
% 2.34/2.56      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.34/2.56  thf('12', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i]:
% 2.34/2.56         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 2.34/2.56      inference('sup-', [status(thm)], ['10', '11'])).
% 2.34/2.56  thf('13', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i]:
% 2.34/2.56         (~ (v1_relat_1 @ X0)
% 2.34/2.56          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.34/2.56             (k1_relat_1 @ X0)))),
% 2.34/2.56      inference('clc', [status(thm)], ['7', '12'])).
% 2.34/2.56  thf('14', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i]:
% 2.34/2.56         ((r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.34/2.56           (k1_relat_1 @ X0))
% 2.34/2.56          | ~ (v1_relat_1 @ X0))),
% 2.34/2.56      inference('sup+', [status(thm)], ['0', '13'])).
% 2.34/2.56  thf('15', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i]:
% 2.34/2.56         (~ (v1_relat_1 @ X0)
% 2.34/2.56          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.34/2.56             (k1_relat_1 @ X0)))),
% 2.34/2.56      inference('clc', [status(thm)], ['7', '12'])).
% 2.34/2.56  thf(t19_xboole_1, axiom,
% 2.34/2.56    (![A:$i,B:$i,C:$i]:
% 2.34/2.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 2.34/2.56       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.34/2.56  thf('16', plain,
% 2.34/2.56      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.34/2.56         (~ (r1_tarski @ X6 @ X7)
% 2.34/2.56          | ~ (r1_tarski @ X6 @ X8)
% 2.34/2.56          | (r1_tarski @ X6 @ (k3_xboole_0 @ X7 @ X8)))),
% 2.34/2.56      inference('cnf', [status(esa)], [t19_xboole_1])).
% 2.34/2.56  thf('17', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.34/2.56         (~ (v1_relat_1 @ X0)
% 2.34/2.56          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.34/2.56             (k3_xboole_0 @ (k1_relat_1 @ X0) @ X2))
% 2.34/2.56          | ~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 2.34/2.56      inference('sup-', [status(thm)], ['15', '16'])).
% 2.34/2.56  thf('18', plain,
% 2.34/2.56      (![X0 : $i, X1 : $i]:
% 2.34/2.56         (~ (v1_relat_1 @ X0)
% 2.34/2.56          | (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.34/2.56             (k3_xboole_0 @ (k1_relat_1 @ X1) @ (k1_relat_1 @ X0)))
% 2.34/2.56          | ~ (v1_relat_1 @ X1))),
% 2.34/2.56      inference('sup-', [status(thm)], ['14', '17'])).
% 2.34/2.56  thf(t14_relat_1, conjecture,
% 2.34/2.56    (![A:$i]:
% 2.34/2.56     ( ( v1_relat_1 @ A ) =>
% 2.34/2.56       ( ![B:$i]:
% 2.34/2.56         ( ( v1_relat_1 @ B ) =>
% 2.34/2.56           ( r1_tarski @
% 2.34/2.56             ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 2.34/2.56             ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 2.34/2.56  thf(zf_stmt_0, negated_conjecture,
% 2.34/2.56    (~( ![A:$i]:
% 2.34/2.56        ( ( v1_relat_1 @ A ) =>
% 2.34/2.56          ( ![B:$i]:
% 2.34/2.56            ( ( v1_relat_1 @ B ) =>
% 2.34/2.56              ( r1_tarski @
% 2.34/2.56                ( k1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 2.34/2.56                ( k3_xboole_0 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) ) ) ) ) )),
% 2.34/2.56    inference('cnf.neg', [status(esa)], [t14_relat_1])).
% 2.34/2.56  thf('19', plain,
% 2.34/2.56      (~ (r1_tarski @ (k1_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 2.34/2.56          (k3_xboole_0 @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B)))),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf('20', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 2.34/2.56      inference('sup-', [status(thm)], ['18', '19'])).
% 2.34/2.56  thf('21', plain, ((v1_relat_1 @ sk_A)),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf('22', plain, ((v1_relat_1 @ sk_B)),
% 2.34/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.34/2.56  thf('23', plain, ($false),
% 2.34/2.56      inference('demod', [status(thm)], ['20', '21', '22'])).
% 2.34/2.56  
% 2.34/2.56  % SZS output end Refutation
% 2.34/2.56  
% 2.34/2.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
