%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lUKYhNGCbn

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:47 EST 2020

% Result     : Theorem 1.16s
% Output     : Refutation 1.16s
% Verified   : 
% Statistics : Number of formulae       :   57 (  82 expanded)
%              Number of leaves         :   21 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  421 ( 687 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X10 @ X11 ) @ ( k3_xboole_0 @ X10 @ X12 ) ) @ ( k2_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( m1_subset_1 @ ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','3'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ) )).

thf('5',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('7',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X16 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k4_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) )
      = ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf('10',plain,(
    ! [X49: $i,X50: $i] :
      ( ( r1_tarski @ X49 @ X50 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ( r1_tarski @ ( k2_relat_1 @ X55 ) @ ( k2_relat_1 @ X54 ) )
      | ~ ( r1_tarski @ X55 @ X54 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X2 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','8'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ( v1_relat_1 @ X52 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['13','16'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X54: $i,X55: $i] :
      ( ~ ( v1_relat_1 @ X54 )
      | ( r1_tarski @ ( k2_relat_1 @ X55 ) @ ( k2_relat_1 @ X54 ) )
      | ~ ( r1_tarski @ X55 @ X54 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('22',plain,(
    ! [X49: $i,X51: $i] :
      ( ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ X51 ) )
      | ~ ( r1_tarski @ X49 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X52: $i,X53: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ( v1_relat_1 @ X52 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','25'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ X9 )
      | ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','28'])).

thf(t27_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_relat_1])).

thf('30',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['31','32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.lUKYhNGCbn
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.16/1.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.16/1.34  % Solved by: fo/fo7.sh
% 1.16/1.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.16/1.34  % done 1192 iterations in 0.894s
% 1.16/1.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.16/1.34  % SZS output start Refutation
% 1.16/1.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.16/1.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.16/1.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.16/1.34  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.16/1.34  thf(sk_A_type, type, sk_A: $i).
% 1.16/1.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.16/1.34  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.16/1.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.16/1.34  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.16/1.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.16/1.34  thf(sk_B_type, type, sk_B: $i).
% 1.16/1.34  thf(t51_xboole_1, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 1.16/1.34       ( A ) ))).
% 1.16/1.34  thf('0', plain,
% 1.16/1.34      (![X16 : $i, X17 : $i]:
% 1.16/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 1.16/1.34           = (X16))),
% 1.16/1.34      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.16/1.34  thf(t31_xboole_1, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( r1_tarski @
% 1.16/1.34       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 1.16/1.34       ( k2_xboole_0 @ B @ C ) ))).
% 1.16/1.34  thf('1', plain,
% 1.16/1.34      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.16/1.34         (r1_tarski @ 
% 1.16/1.34          (k2_xboole_0 @ (k3_xboole_0 @ X10 @ X11) @ (k3_xboole_0 @ X10 @ X12)) @ 
% 1.16/1.34          (k2_xboole_0 @ X11 @ X12))),
% 1.16/1.34      inference('cnf', [status(esa)], [t31_xboole_1])).
% 1.16/1.34  thf(t3_subset, axiom,
% 1.16/1.34    (![A:$i,B:$i]:
% 1.16/1.34     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.16/1.34  thf('2', plain,
% 1.16/1.34      (![X49 : $i, X51 : $i]:
% 1.16/1.34         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 1.16/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.16/1.34  thf('3', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.34         (m1_subset_1 @ 
% 1.16/1.34          (k2_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ (k3_xboole_0 @ X2 @ X0)) @ 
% 1.16/1.34          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['1', '2'])).
% 1.16/1.34  thf('4', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.34         (m1_subset_1 @ 
% 1.16/1.34          (k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.16/1.34           (k3_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))) @ 
% 1.16/1.34          (k1_zfmisc_1 @ X0))),
% 1.16/1.34      inference('sup+', [status(thm)], ['0', '3'])).
% 1.16/1.34  thf(t49_xboole_1, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 1.16/1.34       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) ))).
% 1.16/1.34  thf('5', plain,
% 1.16/1.34      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.16/1.34         ((k3_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 1.16/1.34           = (k4_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15))),
% 1.16/1.34      inference('cnf', [status(esa)], [t49_xboole_1])).
% 1.16/1.34  thf(t16_xboole_1, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.16/1.34       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.16/1.34  thf('6', plain,
% 1.16/1.34      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.16/1.34         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 1.16/1.34           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.16/1.34  thf('7', plain,
% 1.16/1.34      (![X16 : $i, X17 : $i]:
% 1.16/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X16 @ X17) @ (k4_xboole_0 @ X16 @ X17))
% 1.16/1.34           = (X16))),
% 1.16/1.34      inference('cnf', [status(esa)], [t51_xboole_1])).
% 1.16/1.34  thf('8', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.34         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.16/1.34           (k4_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))
% 1.16/1.34           = (k3_xboole_0 @ X2 @ X1))),
% 1.16/1.34      inference('sup+', [status(thm)], ['6', '7'])).
% 1.16/1.34  thf('9', plain,
% 1.16/1.34      (![X0 : $i, X2 : $i]:
% 1.16/1.34         (m1_subset_1 @ (k3_xboole_0 @ X2 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.16/1.34      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.16/1.34  thf('10', plain,
% 1.16/1.34      (![X49 : $i, X50 : $i]:
% 1.16/1.34         ((r1_tarski @ X49 @ X50) | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X50)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.16/1.34  thf('11', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 1.16/1.34      inference('sup-', [status(thm)], ['9', '10'])).
% 1.16/1.34  thf(t25_relat_1, axiom,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( v1_relat_1 @ A ) =>
% 1.16/1.34       ( ![B:$i]:
% 1.16/1.34         ( ( v1_relat_1 @ B ) =>
% 1.16/1.34           ( ( r1_tarski @ A @ B ) =>
% 1.16/1.34             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.16/1.34               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.16/1.34  thf('12', plain,
% 1.16/1.34      (![X54 : $i, X55 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ X54)
% 1.16/1.34          | (r1_tarski @ (k2_relat_1 @ X55) @ (k2_relat_1 @ X54))
% 1.16/1.34          | ~ (r1_tarski @ X55 @ X54)
% 1.16/1.34          | ~ (v1_relat_1 @ X55))),
% 1.16/1.34      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.16/1.34  thf('13', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 1.16/1.34          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.16/1.34             (k2_relat_1 @ X0))
% 1.16/1.34          | ~ (v1_relat_1 @ X0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['11', '12'])).
% 1.16/1.34  thf('14', plain,
% 1.16/1.34      (![X0 : $i, X2 : $i]:
% 1.16/1.34         (m1_subset_1 @ (k3_xboole_0 @ X2 @ X0) @ (k1_zfmisc_1 @ X0))),
% 1.16/1.34      inference('demod', [status(thm)], ['4', '5', '8'])).
% 1.16/1.34  thf(cc2_relat_1, axiom,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( v1_relat_1 @ A ) =>
% 1.16/1.34       ( ![B:$i]:
% 1.16/1.34         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.16/1.34  thf('15', plain,
% 1.16/1.34      (![X52 : $i, X53 : $i]:
% 1.16/1.34         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53))
% 1.16/1.34          | (v1_relat_1 @ X52)
% 1.16/1.34          | ~ (v1_relat_1 @ X53))),
% 1.16/1.34      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.16/1.34  thf('16', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['14', '15'])).
% 1.16/1.34  thf('17', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ X0)
% 1.16/1.34          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.16/1.34             (k2_relat_1 @ X0)))),
% 1.16/1.34      inference('clc', [status(thm)], ['13', '16'])).
% 1.16/1.34  thf(t17_xboole_1, axiom,
% 1.16/1.34    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.16/1.34  thf('18', plain,
% 1.16/1.34      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 1.16/1.34      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.16/1.34  thf('19', plain,
% 1.16/1.34      (![X54 : $i, X55 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ X54)
% 1.16/1.34          | (r1_tarski @ (k2_relat_1 @ X55) @ (k2_relat_1 @ X54))
% 1.16/1.34          | ~ (r1_tarski @ X55 @ X54)
% 1.16/1.34          | ~ (v1_relat_1 @ X55))),
% 1.16/1.34      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.16/1.34  thf('20', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 1.16/1.34          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.16/1.34             (k2_relat_1 @ X0))
% 1.16/1.34          | ~ (v1_relat_1 @ X0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['18', '19'])).
% 1.16/1.34  thf('21', plain,
% 1.16/1.34      (![X5 : $i, X6 : $i]: (r1_tarski @ (k3_xboole_0 @ X5 @ X6) @ X5)),
% 1.16/1.34      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.16/1.34  thf('22', plain,
% 1.16/1.34      (![X49 : $i, X51 : $i]:
% 1.16/1.34         ((m1_subset_1 @ X49 @ (k1_zfmisc_1 @ X51)) | ~ (r1_tarski @ X49 @ X51))),
% 1.16/1.34      inference('cnf', [status(esa)], [t3_subset])).
% 1.16/1.34  thf('23', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.16/1.34      inference('sup-', [status(thm)], ['21', '22'])).
% 1.16/1.34  thf('24', plain,
% 1.16/1.34      (![X52 : $i, X53 : $i]:
% 1.16/1.34         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53))
% 1.16/1.34          | (v1_relat_1 @ X52)
% 1.16/1.34          | ~ (v1_relat_1 @ X53))),
% 1.16/1.34      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.16/1.34  thf('25', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.16/1.34      inference('sup-', [status(thm)], ['23', '24'])).
% 1.16/1.34  thf('26', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ X0)
% 1.16/1.34          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.16/1.34             (k2_relat_1 @ X0)))),
% 1.16/1.34      inference('clc', [status(thm)], ['20', '25'])).
% 1.16/1.34  thf(t19_xboole_1, axiom,
% 1.16/1.34    (![A:$i,B:$i,C:$i]:
% 1.16/1.34     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.16/1.34       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.16/1.34  thf('27', plain,
% 1.16/1.34      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.16/1.34         (~ (r1_tarski @ X7 @ X8)
% 1.16/1.34          | ~ (r1_tarski @ X7 @ X9)
% 1.16/1.34          | (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 1.16/1.34      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.16/1.34  thf('28', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ X0)
% 1.16/1.34          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.16/1.34             (k3_xboole_0 @ (k2_relat_1 @ X0) @ X2))
% 1.16/1.34          | ~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 1.16/1.34      inference('sup-', [status(thm)], ['26', '27'])).
% 1.16/1.34  thf('29', plain,
% 1.16/1.34      (![X0 : $i, X1 : $i]:
% 1.16/1.34         (~ (v1_relat_1 @ X0)
% 1.16/1.34          | (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.16/1.34             (k3_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)))
% 1.16/1.34          | ~ (v1_relat_1 @ X1))),
% 1.16/1.34      inference('sup-', [status(thm)], ['17', '28'])).
% 1.16/1.34  thf(t27_relat_1, conjecture,
% 1.16/1.34    (![A:$i]:
% 1.16/1.34     ( ( v1_relat_1 @ A ) =>
% 1.16/1.34       ( ![B:$i]:
% 1.16/1.34         ( ( v1_relat_1 @ B ) =>
% 1.16/1.34           ( r1_tarski @
% 1.16/1.34             ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.16/1.34             ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 1.16/1.34  thf(zf_stmt_0, negated_conjecture,
% 1.16/1.34    (~( ![A:$i]:
% 1.16/1.34        ( ( v1_relat_1 @ A ) =>
% 1.16/1.34          ( ![B:$i]:
% 1.16/1.34            ( ( v1_relat_1 @ B ) =>
% 1.16/1.34              ( r1_tarski @
% 1.16/1.34                ( k2_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 1.16/1.34                ( k3_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 1.16/1.34    inference('cnf.neg', [status(esa)], [t27_relat_1])).
% 1.16/1.34  thf('30', plain,
% 1.16/1.34      (~ (r1_tarski @ (k2_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 1.16/1.34          (k3_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('31', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 1.16/1.34      inference('sup-', [status(thm)], ['29', '30'])).
% 1.16/1.34  thf('32', plain, ((v1_relat_1 @ sk_A)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 1.16/1.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.16/1.34  thf('34', plain, ($false),
% 1.16/1.34      inference('demod', [status(thm)], ['31', '32', '33'])).
% 1.16/1.34  
% 1.16/1.34  % SZS output end Refutation
% 1.16/1.34  
% 1.16/1.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
