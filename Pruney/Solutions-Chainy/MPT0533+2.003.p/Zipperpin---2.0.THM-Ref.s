%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cNC4zytdpY

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:44 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :   10
%              Number of atoms          :  333 ( 524 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( v1_relat_1 @ X12 )
      | ( ( k8_relat_1 @ X11 @ ( k8_relat_1 @ X10 @ X12 ) )
        = ( k8_relat_1 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_B @ ( k8_relat_1 @ sk_A @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X8 @ X9 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf(t132_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k8_relat_1 @ X14 @ X15 ) @ ( k8_relat_1 @ X14 @ X13 ) )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X8 @ X9 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X2 @ ( k8_relat_1 @ X1 @ X0 ) ) @ ( k8_relat_1 @ X2 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k8_relat_1 @ X14 @ X15 ) @ ( k8_relat_1 @ X14 @ X13 ) )
      | ~ ( r1_tarski @ X15 @ X13 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t132_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ ( k8_relat_1 @ X0 @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ ( k8_relat_1 @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_C ) @ X1 )
      | ~ ( r1_tarski @ ( k8_relat_1 @ X0 @ sk_D ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C ) @ ( k8_relat_1 @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['0','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.cNC4zytdpY
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 59 iterations in 0.043s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(t133_relat_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ![D:$i]:
% 0.19/0.49         ( ( v1_relat_1 @ D ) =>
% 0.19/0.49           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.19/0.49             ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ( v1_relat_1 @ C ) =>
% 0.19/0.49          ( ![D:$i]:
% 0.19/0.49            ( ( v1_relat_1 @ D ) =>
% 0.19/0.49              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.19/0.49                ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ D ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t133_relat_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_D))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t129_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ C ) =>
% 0.19/0.49       ( ( r1_tarski @ A @ B ) =>
% 0.19/0.49         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X10 @ X11)
% 0.19/0.49          | ~ (v1_relat_1 @ X12)
% 0.19/0.49          | ((k8_relat_1 @ X11 @ (k8_relat_1 @ X10 @ X12))
% 0.19/0.49              = (k8_relat_1 @ X10 @ X12)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t129_relat_1])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((k8_relat_1 @ sk_B @ (k8_relat_1 @ sk_A @ X0))
% 0.19/0.49            = (k8_relat_1 @ sk_A @ X0))
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.49  thf(t117_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i]:
% 0.19/0.49         ((r1_tarski @ (k8_relat_1 @ X8 @ X9) @ X9) | ~ (v1_relat_1 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.19/0.49  thf(t132_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ B ) =>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( v1_relat_1 @ C ) =>
% 0.19/0.49           ( ( r1_tarski @ B @ C ) =>
% 0.19/0.49             ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ ( k8_relat_1 @ A @ C ) ) ) ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X13)
% 0.19/0.49          | (r1_tarski @ (k8_relat_1 @ X14 @ X15) @ (k8_relat_1 @ X14 @ X13))
% 0.19/0.49          | ~ (r1_tarski @ X15 @ X13)
% 0.19/0.49          | ~ (v1_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [t132_relat_1])).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.49          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.19/0.49             (k8_relat_1 @ X2 @ X0))
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         ((r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.19/0.49           (k8_relat_1 @ X2 @ X0))
% 0.19/0.49          | ~ (v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i]:
% 0.19/0.49         ((r1_tarski @ (k8_relat_1 @ X8 @ X9) @ X9) | ~ (v1_relat_1 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.19/0.49  thf(t3_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X3 : $i, X5 : $i]:
% 0.19/0.49         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | (m1_subset_1 @ (k8_relat_1 @ X1 @ X0) @ (k1_zfmisc_1 @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.49  thf(cc2_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.19/0.49          | (v1_relat_1 @ X6)
% 0.19/0.49          | ~ (v1_relat_1 @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ X0)
% 0.19/0.49          | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('simplify', [status(thm)], ['12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | (r1_tarski @ (k8_relat_1 @ X2 @ (k8_relat_1 @ X1 @ X0)) @ 
% 0.19/0.49             (k8_relat_1 @ X2 @ X0)))),
% 0.19/0.49      inference('clc', [status(thm)], ['7', '13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B @ X0))
% 0.19/0.49          | ~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['3', '14'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B @ X0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.49  thf('17', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X13)
% 0.19/0.49          | (r1_tarski @ (k8_relat_1 @ X14 @ X15) @ (k8_relat_1 @ X14 @ X13))
% 0.19/0.49          | ~ (r1_tarski @ X15 @ X13)
% 0.19/0.49          | ~ (v1_relat_1 @ X15))),
% 0.19/0.49      inference('cnf', [status(esa)], [t132_relat_1])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ sk_C)
% 0.19/0.49          | (r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ (k8_relat_1 @ X0 @ sk_D))
% 0.19/0.49          | ~ (v1_relat_1 @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.49  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('21', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ (k8_relat_1 @ X0 @ sk_D))),
% 0.19/0.49      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.19/0.49  thf(t1_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.19/0.49       ( r1_tarski @ A @ C ) ))).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (~ (r1_tarski @ X0 @ X1)
% 0.19/0.49          | ~ (r1_tarski @ X1 @ X2)
% 0.19/0.49          | (r1_tarski @ X0 @ X2))),
% 0.19/0.49      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_tarski @ (k8_relat_1 @ X0 @ sk_C) @ X1)
% 0.19/0.49          | ~ (r1_tarski @ (k8_relat_1 @ X0 @ sk_D) @ X1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ sk_D)
% 0.19/0.50        | (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_D)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '24'])).
% 0.19/0.50  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      ((r1_tarski @ (k8_relat_1 @ sk_A @ sk_C) @ (k8_relat_1 @ sk_B @ sk_D))),
% 0.19/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('28', plain, ($false), inference('demod', [status(thm)], ['0', '27'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
