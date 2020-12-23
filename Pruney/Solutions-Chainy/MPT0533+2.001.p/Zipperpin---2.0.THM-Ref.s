%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k7wWKr4Ozb

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:44 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (  84 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :  365 ( 722 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t133_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t133_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t116_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X8 @ X9 ) ) @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t116_relat_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ X0 @ X1 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ( ( k8_relat_1 @ X13 @ X12 )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_A @ X0 ) )
      | ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X10 @ X11 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k8_relat_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['7','13'])).

thf('15',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X10 @ X11 ) @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ sk_D )
      | ~ ( v1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t132_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( r1_tarski @ ( k8_relat_1 @ X15 @ X16 ) @ ( k8_relat_1 @ X15 @ X14 ) )
      | ~ ( r1_tarski @ X16 @ X14 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_C ) )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C ) ) @ ( k8_relat_1 @ X1 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('25',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k8_relat_1 @ X0 @ sk_C ) @ ( k1_zfmisc_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k8_relat_1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X1 @ ( k8_relat_1 @ X0 @ sk_C ) ) @ ( k8_relat_1 @ X1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['23','30','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['14','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.k7wWKr4Ozb
% 0.13/0.36  % Computer   : n016.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 15:52:19 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 100 iterations in 0.039s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(t133_relat_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ C ) =>
% 0.22/0.49       ( ![D:$i]:
% 0.22/0.49         ( ( v1_relat_1 @ D ) =>
% 0.22/0.49           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.22/0.49             ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.49        ( ( v1_relat_1 @ C ) =>
% 0.22/0.49          ( ![D:$i]:
% 0.22/0.49            ( ( v1_relat_1 @ D ) =>
% 0.22/0.49              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.22/0.49                ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t133_relat_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_D))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t116_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( r1_tarski @ ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) @ A ) ))).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      (![X8 : $i, X9 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X8 @ X9)) @ X8)
% 0.22/0.49          | ~ (v1_relat_1 @ X9))),
% 0.22/0.49      inference('cnf', [status(esa)], [t116_relat_1])).
% 0.22/0.49  thf(t1_xboole_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i]:
% 0.22/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.49       ( r1_tarski @ A @ C ) ))).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.49          | ~ (r1_tarski @ X1 @ X2)
% 0.22/0.49          | (r1_tarski @ X0 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X1)
% 0.22/0.49          | (r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ X0 @ X1)) @ X2)
% 0.22/0.49          | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k2_relat_1 @ (k8_relat_1 @ sk_A @ X0)) @ sk_B)
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.49  thf(t125_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.22/0.49         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.22/0.49  thf('6', plain,
% 0.22/0.49      (![X12 : $i, X13 : $i]:
% 0.22/0.49         (~ (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.22/0.49          | ((k8_relat_1 @ X13 @ X12) = (X12))
% 0.22/0.49          | ~ (v1_relat_1 @ X12))),
% 0.22/0.49      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.22/0.49  thf('7', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_A @ X0))
% 0.22/0.49          | ((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.22/0.49              = (k8_relat_1 @ sk_A @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.49  thf(t117_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.22/0.49  thf('8', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         ((r1_tarski @ (k8_relat_1 @ X10 @ X11) @ X11) | ~ (v1_relat_1 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.22/0.49  thf(t3_subset, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.49  thf('9', plain,
% 0.22/0.49      (![X3 : $i, X5 : $i]:
% 0.22/0.49         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | (m1_subset_1 @ (k8_relat_1 @ X1 @ X0) @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.49  thf(cc2_relat_1, axiom,
% 0.22/0.49    (![A:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ A ) =>
% 0.22/0.49       ( ![B:$i]:
% 0.22/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.22/0.49          | (v1_relat_1 @ X6)
% 0.22/0.49          | ~ (v1_relat_1 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | ~ (v1_relat_1 @ X0)
% 0.22/0.49          | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.22/0.49  thf('14', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.22/0.49            = (k8_relat_1 @ sk_A @ X0))
% 0.22/0.49          | ~ (v1_relat_1 @ X0))),
% 0.22/0.49      inference('clc', [status(thm)], ['7', '13'])).
% 0.22/0.49  thf('15', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('16', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i]:
% 0.22/0.49         ((r1_tarski @ (k8_relat_1 @ X10 @ X11) @ X11) | ~ (v1_relat_1 @ X11))),
% 0.22/0.49      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.22/0.49  thf('17', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.49          | ~ (r1_tarski @ X1 @ X2)
% 0.22/0.49          | (r1_tarski @ X0 @ X2))),
% 0.22/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X0)
% 0.22/0.49          | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X2)
% 0.22/0.49          | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.49      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ sk_D) | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup-', [status(thm)], ['15', '18'])).
% 0.22/0.49  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('21', plain, (![X0 : $i]: (r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ sk_D)),
% 0.22/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf(t132_relat_1, axiom,
% 0.22/0.49    (![A:$i,B:$i]:
% 0.22/0.49     ( ( v1_relat_1 @ B ) =>
% 0.22/0.49       ( ![C:$i]:
% 0.22/0.49         ( ( v1_relat_1 @ C ) =>
% 0.22/0.49           ( ( r1_tarski @ B @ C ) =>
% 0.22/0.49             ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.22/0.49  thf('22', plain,
% 0.22/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ X14)
% 0.22/0.49          | (r1_tarski @ (k8_relat_1 @ X15 @ X16) @ (k8_relat_1 @ X15 @ X14))
% 0.22/0.49          | ~ (r1_tarski @ X16 @ X14)
% 0.22/0.49          | ~ (v1_relat_1 @ X16))),
% 0.22/0.49      inference('cnf', [status(esa)], [t132_relat_1])).
% 0.22/0.49  thf('23', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_C))
% 0.22/0.49          | (r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C)) @ 
% 0.22/0.49             (k8_relat_1 @ X1 @ sk_D))
% 0.22/0.49          | ~ (v1_relat_1 @ sk_D))),
% 0.22/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.49  thf('24', plain, (![X0 : $i]: (r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ sk_D)),
% 0.22/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('25', plain,
% 0.22/0.49      (![X3 : $i, X5 : $i]:
% 0.22/0.49         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.22/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (m1_subset_1 @ (k8_relat_1 @ X0 @ sk_C) @ (k1_zfmisc_1 @ sk_D))),
% 0.22/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      (![X6 : $i, X7 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.22/0.49          | (v1_relat_1 @ X6)
% 0.22/0.49          | ~ (v1_relat_1 @ X7))),
% 0.22/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X0 : $i]:
% 0.22/0.49         (~ (v1_relat_1 @ sk_D) | (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_C)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.49  thf('29', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('30', plain, (![X0 : $i]: (v1_relat_1 @ (k8_relat_1 @ X0 @ sk_C))),
% 0.22/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.22/0.49  thf('31', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('32', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i]:
% 0.22/0.49         (r1_tarski @ (k8_relat_1 @ X1 @ (k8_relat_1 @ X0 @ sk_C)) @ 
% 0.22/0.49          (k8_relat_1 @ X1 @ sk_D))),
% 0.22/0.49      inference('demod', [status(thm)], ['23', '30', '31'])).
% 0.22/0.49  thf('33', plain,
% 0.22/0.49      (((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_D))
% 0.22/0.49        | ~ (v1_relat_1 @ sk_C))),
% 0.22/0.49      inference('sup+', [status(thm)], ['14', '32'])).
% 0.22/0.49  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_D))),
% 0.22/0.49      inference('demod', [status(thm)], ['33', '34'])).
% 0.22/0.49  thf('36', plain, ($false), inference('demod', [status(thm)], ['0', '35'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
