%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YqHu71SxlT

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 (  65 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  428 ( 555 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X8 @ X9 ) )
        = ( k9_relat_1 @ X8 @ X9 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k10_relat_1 @ X10 @ X11 )
        = ( k10_relat_1 @ X10 @ ( k3_xboole_0 @ ( k2_relat_1 @ X10 ) @ X11 ) ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
        = ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ ( k3_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ X2 ) ) ) ) ),
    inference(clc,[status(thm)],['2','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('13',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t180_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k10_relat_1 @ X13 @ X14 ) @ ( k10_relat_1 @ X12 @ X15 ) )
      | ~ ( r1_tarski @ X13 @ X12 )
      | ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t180_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X3 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ X3 ) @ ( k10_relat_1 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X3 ) @ ( k10_relat_1 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X3 ) @ ( k10_relat_1 @ X1 @ X2 ) )
      | ~ ( r1_tarski @ X3 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X1 @ X2 ) @ X0 ) @ ( k10_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['9','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) @ ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t139_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X19 @ X18 ) @ X20 )
        = ( k3_xboole_0 @ X18 @ ( k10_relat_1 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t139_funct_1])).

thf(t151_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( r1_tarski @ ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_funct_1])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B ) ) @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B ) @ ( k10_relat_1 @ sk_C @ ( k3_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YqHu71SxlT
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.53  % Solved by: fo/fo7.sh
% 0.19/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.53  % done 61 iterations in 0.081s
% 0.19/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.53  % SZS output start Refutation
% 0.19/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.53  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.19/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.19/0.53  thf(t148_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ B ) =>
% 0.19/0.53       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.19/0.53  thf('0', plain,
% 0.19/0.53      (![X8 : $i, X9 : $i]:
% 0.19/0.53         (((k2_relat_1 @ (k7_relat_1 @ X8 @ X9)) = (k9_relat_1 @ X8 @ X9))
% 0.19/0.53          | ~ (v1_relat_1 @ X8))),
% 0.19/0.53      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.19/0.53  thf(t168_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ B ) =>
% 0.19/0.53       ( ( k10_relat_1 @ B @ A ) =
% 0.19/0.53         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.19/0.53  thf('1', plain,
% 0.19/0.53      (![X10 : $i, X11 : $i]:
% 0.19/0.53         (((k10_relat_1 @ X10 @ X11)
% 0.19/0.53            = (k10_relat_1 @ X10 @ (k3_xboole_0 @ (k2_relat_1 @ X10) @ X11)))
% 0.19/0.53          | ~ (v1_relat_1 @ X10))),
% 0.19/0.53      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.19/0.53  thf('2', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.53            = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.19/0.53               (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2)))
% 0.19/0.53          | ~ (v1_relat_1 @ X1)
% 0.19/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.19/0.53      inference('sup+', [status(thm)], ['0', '1'])).
% 0.19/0.53  thf(t88_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.19/0.53  thf('3', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i]:
% 0.19/0.53         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 0.19/0.53      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.19/0.53  thf(t3_subset, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.53  thf('4', plain,
% 0.19/0.53      (![X3 : $i, X5 : $i]:
% 0.19/0.53         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.19/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.53  thf('5', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X0)
% 0.19/0.53          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.19/0.53  thf(cc2_relat_1, axiom,
% 0.19/0.53    (![A:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ A ) =>
% 0.19/0.53       ( ![B:$i]:
% 0.19/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.53  thf('6', plain,
% 0.19/0.53      (![X6 : $i, X7 : $i]:
% 0.19/0.53         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.19/0.53          | (v1_relat_1 @ X6)
% 0.19/0.53          | ~ (v1_relat_1 @ X7))),
% 0.19/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.53  thf('7', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ X0)
% 0.19/0.53          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.53  thf('8', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.53  thf('9', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X1)
% 0.19/0.53          | ((k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2)
% 0.19/0.53              = (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ 
% 0.19/0.53                 (k3_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ X2))))),
% 0.19/0.53      inference('clc', [status(thm)], ['2', '8'])).
% 0.19/0.53  thf(d10_xboole_0, axiom,
% 0.19/0.53    (![A:$i,B:$i]:
% 0.19/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.53  thf('10', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.53  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.53      inference('simplify', [status(thm)], ['10'])).
% 0.19/0.53  thf('12', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i]:
% 0.19/0.53         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['7'])).
% 0.19/0.53  thf('13', plain,
% 0.19/0.53      (![X16 : $i, X17 : $i]:
% 0.19/0.53         ((r1_tarski @ (k7_relat_1 @ X16 @ X17) @ X16) | ~ (v1_relat_1 @ X16))),
% 0.19/0.53      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.19/0.53  thf(t180_relat_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ C ) =>
% 0.19/0.53       ( ![D:$i]:
% 0.19/0.53         ( ( v1_relat_1 @ D ) =>
% 0.19/0.53           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.19/0.53             ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.19/0.53  thf('14', plain,
% 0.19/0.53      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X12)
% 0.19/0.53          | (r1_tarski @ (k10_relat_1 @ X13 @ X14) @ (k10_relat_1 @ X12 @ X15))
% 0.19/0.53          | ~ (r1_tarski @ X13 @ X12)
% 0.19/0.53          | ~ (r1_tarski @ X14 @ X15)
% 0.19/0.53          | ~ (v1_relat_1 @ X13))),
% 0.19/0.53      inference('cnf', [status(esa)], [t180_relat_1])).
% 0.19/0.53  thf('15', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X0)
% 0.19/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.19/0.53          | ~ (r1_tarski @ X3 @ X2)
% 0.19/0.53          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X3) @ 
% 0.19/0.53             (k10_relat_1 @ X0 @ X2))
% 0.19/0.53          | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.53  thf('16', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X0 @ X1) @ X3) @ 
% 0.19/0.53           (k10_relat_1 @ X0 @ X2))
% 0.19/0.53          | ~ (r1_tarski @ X3 @ X2)
% 0.19/0.53          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.19/0.53          | ~ (v1_relat_1 @ X0))),
% 0.19/0.53      inference('simplify', [status(thm)], ['15'])).
% 0.19/0.53  thf('17', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X1)
% 0.19/0.53          | ~ (v1_relat_1 @ X1)
% 0.19/0.53          | ~ (r1_tarski @ X3 @ X2)
% 0.19/0.53          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X3) @ 
% 0.19/0.53             (k10_relat_1 @ X1 @ X2)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['12', '16'])).
% 0.19/0.53  thf('18', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.53         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X3) @ 
% 0.19/0.53           (k10_relat_1 @ X1 @ X2))
% 0.19/0.53          | ~ (r1_tarski @ X3 @ X2)
% 0.19/0.53          | ~ (v1_relat_1 @ X1))),
% 0.19/0.53      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.53  thf('19', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X1)
% 0.19/0.53          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X1 @ X2) @ X0) @ 
% 0.19/0.53             (k10_relat_1 @ X1 @ X0)))),
% 0.19/0.53      inference('sup-', [status(thm)], ['11', '18'])).
% 0.19/0.53  thf('20', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 0.19/0.53           (k10_relat_1 @ X2 @ (k3_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ X0)))
% 0.19/0.53          | ~ (v1_relat_1 @ X2)
% 0.19/0.53          | ~ (v1_relat_1 @ X2))),
% 0.19/0.53      inference('sup+', [status(thm)], ['9', '19'])).
% 0.19/0.53  thf('21', plain,
% 0.19/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.53         (~ (v1_relat_1 @ X2)
% 0.19/0.53          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) @ 
% 0.19/0.53             (k10_relat_1 @ X2 @ (k3_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ X0))))),
% 0.19/0.53      inference('simplify', [status(thm)], ['20'])).
% 0.19/0.53  thf(t139_funct_1, axiom,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ C ) =>
% 0.19/0.53       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.19/0.53         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.19/0.53  thf('22', plain,
% 0.19/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.19/0.53         (((k10_relat_1 @ (k7_relat_1 @ X19 @ X18) @ X20)
% 0.19/0.53            = (k3_xboole_0 @ X18 @ (k10_relat_1 @ X19 @ X20)))
% 0.19/0.53          | ~ (v1_relat_1 @ X19))),
% 0.19/0.53      inference('cnf', [status(esa)], [t139_funct_1])).
% 0.19/0.53  thf(t151_funct_1, conjecture,
% 0.19/0.53    (![A:$i,B:$i,C:$i]:
% 0.19/0.53     ( ( v1_relat_1 @ C ) =>
% 0.19/0.53       ( r1_tarski @
% 0.19/0.53         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ 
% 0.19/0.53         ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ))).
% 0.19/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.53        ( ( v1_relat_1 @ C ) =>
% 0.19/0.53          ( r1_tarski @
% 0.19/0.53            ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) @ 
% 0.19/0.53            ( k10_relat_1 @ C @ ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ B ) ) ) ) )),
% 0.19/0.53    inference('cnf.neg', [status(esa)], [t151_funct_1])).
% 0.19/0.53  thf('23', plain,
% 0.19/0.53      (~ (r1_tarski @ (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B)) @ 
% 0.19/0.53          (k10_relat_1 @ sk_C @ 
% 0.19/0.53           (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('24', plain,
% 0.19/0.53      ((~ (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) @ 
% 0.19/0.53           (k10_relat_1 @ sk_C @ 
% 0.19/0.53            (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)))
% 0.19/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.53  thf('25', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('26', plain,
% 0.19/0.53      (~ (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B) @ 
% 0.19/0.53          (k10_relat_1 @ sk_C @ 
% 0.19/0.53           (k3_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ sk_B)))),
% 0.19/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.53  thf('27', plain, (~ (v1_relat_1 @ sk_C)),
% 0.19/0.53      inference('sup-', [status(thm)], ['21', '26'])).
% 0.19/0.53  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.53  thf('29', plain, ($false), inference('demod', [status(thm)], ['27', '28'])).
% 0.19/0.53  
% 0.19/0.53  % SZS output end Refutation
% 0.19/0.53  
% 0.19/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
