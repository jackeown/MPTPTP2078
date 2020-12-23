%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HGdAwMEm4G

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:48 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   35 (  41 expanded)
%              Number of leaves         :   17 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  164 ( 254 expanded)
%              Number of equality atoms :   13 (  19 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('0',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_subset_1 @ X12 @ X13 )
        = ( k4_xboole_0 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X11 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('7',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ sk_C ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( r1_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['7','10'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup+',[status(thm)],['2','13'])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.HGdAwMEm4G
% 0.15/0.39  % Computer   : n025.cluster.edu
% 0.15/0.39  % Model      : x86_64 x86_64
% 0.15/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.39  % Memory     : 8042.1875MB
% 0.15/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.39  % CPULimit   : 60
% 0.15/0.39  % DateTime   : Tue Dec  1 17:36:21 EST 2020
% 0.15/0.39  % CPUTime    : 
% 0.15/0.39  % Running portfolio for 600 s
% 0.15/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.39  % Number of cores: 8
% 0.15/0.39  % Python version: Python 3.6.8
% 0.15/0.39  % Running in FO mode
% 0.24/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.48  % Solved by: fo/fo7.sh
% 0.24/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.48  % done 59 iterations in 0.020s
% 0.24/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.48  % SZS output start Refutation
% 0.24/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.48  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.24/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.24/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.48  thf(t40_subset_1, conjecture,
% 0.24/0.48    (![A:$i,B:$i,C:$i]:
% 0.24/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.48       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.24/0.48         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.24/0.48        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.48          ( ( ( r1_tarski @ B @ C ) & 
% 0.24/0.48              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.24/0.48            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.24/0.48    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.24/0.48  thf('0', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf(t28_xboole_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.24/0.48  thf('1', plain,
% 0.24/0.48      (![X5 : $i, X6 : $i]:
% 0.24/0.48         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.24/0.48      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.24/0.48  thf('2', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.24/0.48      inference('sup-', [status(thm)], ['0', '1'])).
% 0.24/0.48  thf('3', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf(d5_subset_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.24/0.48       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.24/0.48  thf('4', plain,
% 0.24/0.48      (![X12 : $i, X13 : $i]:
% 0.24/0.48         (((k3_subset_1 @ X12 @ X13) = (k4_xboole_0 @ X12 @ X13))
% 0.24/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X12)))),
% 0.24/0.48      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.24/0.48  thf('5', plain,
% 0.24/0.48      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.24/0.48      inference('sup-', [status(thm)], ['3', '4'])).
% 0.24/0.48  thf(t79_xboole_1, axiom,
% 0.24/0.48    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.24/0.48  thf('6', plain,
% 0.24/0.48      (![X10 : $i, X11 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X11)),
% 0.24/0.48      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.24/0.48  thf('7', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ sk_C)),
% 0.24/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.24/0.48  thf('8', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf(t63_xboole_1, axiom,
% 0.24/0.48    (![A:$i,B:$i,C:$i]:
% 0.24/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.24/0.48       ( r1_xboole_0 @ A @ C ) ))).
% 0.24/0.48  thf('9', plain,
% 0.24/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.48         (~ (r1_tarski @ X7 @ X8)
% 0.24/0.48          | ~ (r1_xboole_0 @ X8 @ X9)
% 0.24/0.48          | (r1_xboole_0 @ X7 @ X9))),
% 0.24/0.48      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.24/0.48  thf('10', plain,
% 0.24/0.48      (![X0 : $i]:
% 0.24/0.48         ((r1_xboole_0 @ sk_B @ X0)
% 0.24/0.48          | ~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C) @ X0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.24/0.48  thf('11', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.24/0.48      inference('sup-', [status(thm)], ['7', '10'])).
% 0.24/0.48  thf(d7_xboole_0, axiom,
% 0.24/0.48    (![A:$i,B:$i]:
% 0.24/0.48     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.24/0.48       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.48  thf('12', plain,
% 0.24/0.48      (![X0 : $i, X1 : $i]:
% 0.24/0.48         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.24/0.48      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.24/0.48  thf('13', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_xboole_0))),
% 0.24/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.48  thf('14', plain, (((sk_B) = (k1_xboole_0))),
% 0.24/0.48      inference('sup+', [status(thm)], ['2', '13'])).
% 0.24/0.48  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.24/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.48  thf('16', plain, ($false),
% 0.24/0.48      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.24/0.48  
% 0.24/0.48  % SZS output end Refutation
% 0.24/0.48  
% 0.24/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
