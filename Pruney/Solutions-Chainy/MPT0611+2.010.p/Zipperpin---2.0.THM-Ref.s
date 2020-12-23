%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LHWsf1lrg3

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  246 ( 327 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t215_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( r1_xboole_0 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
             => ( r1_xboole_0 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t215_relat_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('2',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t127_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_xboole_0 @ A @ B )
        | ( r1_xboole_0 @ C @ D ) )
     => ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X12 @ X13 ) @ ( k2_zfmisc_1 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t127_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ sk_A ) ) @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X16: $i] :
      ( ( r1_tarski @ X16 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X16 ) @ ( k2_relat_1 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
        = ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X5 @ ( k2_xboole_0 @ X6 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X10 )
        = X9 )
      | ~ ( r1_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_A ) ) @ sk_B )
      = ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_A ) ) )
      | ( r1_xboole_0 @ X1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LHWsf1lrg3
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:55:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 40 iterations in 0.028s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(t215_relat_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( v1_relat_1 @ B ) =>
% 0.20/0.49           ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.49             ( r1_xboole_0 @ A @ B ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( v1_relat_1 @ A ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( v1_relat_1 @ B ) =>
% 0.20/0.49              ( ( r1_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.20/0.49                ( r1_xboole_0 @ A @ B ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t215_relat_1])).
% 0.20/0.49  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t21_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( r1_tarski @
% 0.20/0.49         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X16 : $i]:
% 0.20/0.49         ((r1_tarski @ X16 @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 0.20/0.49          | ~ (v1_relat_1 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.49  thf('2', plain, ((r1_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t127_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( ( r1_xboole_0 @ A @ B ) | ( r1_xboole_0 @ C @ D ) ) =>
% 0.20/0.49       ( r1_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k2_zfmisc_1 @ X12 @ X13) @ (k2_zfmisc_1 @ X14 @ X15))
% 0.20/0.49          | ~ (r1_xboole_0 @ X13 @ X15))),
% 0.20/0.49      inference('cnf', [status(esa)], [t127_zfmisc_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (r1_xboole_0 @ (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ sk_A)) @ 
% 0.20/0.49          (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X16 : $i]:
% 0.20/0.49         ((r1_tarski @ X16 @ 
% 0.20/0.49           (k2_zfmisc_1 @ (k1_relat_1 @ X16) @ (k2_relat_1 @ X16)))
% 0.20/0.49          | ~ (v1_relat_1 @ X16))),
% 0.20/0.49      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.20/0.49  thf(t12_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | ((k2_xboole_0 @ X0 @ 
% 0.20/0.49              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.20/0.49              = (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf(t70_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X5 @ X6)
% 0.20/0.49          | ~ (r1_xboole_0 @ X5 @ (k2_xboole_0 @ X6 @ X8)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ X1 @ 
% 0.20/0.49             (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_A)) @ sk_B)
% 0.20/0.49          | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '9'])).
% 0.20/0.49  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (r1_xboole_0 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_A)) @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf(t83_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ X9 @ X10) = (X9)) | ~ (r1_xboole_0 @ X9 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k4_xboole_0 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_A)) @ sk_B)
% 0.20/0.49           = (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.49  thf(t106_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.20/0.49       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X2)
% 0.20/0.49          | ~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_tarski @ X1 @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_A)))
% 0.20/0.49          | (r1_xboole_0 @ X1 @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain, ((~ (v1_relat_1 @ sk_A) | (r1_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '16'])).
% 0.20/0.49  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.49  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
