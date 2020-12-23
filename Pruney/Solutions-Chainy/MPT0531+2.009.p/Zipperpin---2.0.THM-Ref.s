%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h4PwXZJpqJ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 124 expanded)
%              Number of leaves         :   34 (  52 expanded)
%              Depth                    :   17
%              Number of atoms          :  492 ( 848 expanded)
%              Number of equality atoms :   33 (  45 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('0',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X18 @ X19 ) @ X19 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t131_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t131_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('8',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X2 @ X5 ) )
      | ~ ( r1_xboole_0 @ X2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) )
      = ( k4_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) )
      = ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_1 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['15','16','17'])).

thf(t101_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ X7 @ X8 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X7 @ X8 ) @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t101_xboole_1])).

thf('20',plain,
    ( ( k5_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('22',plain,(
    ! [X9: $i] :
      ( ( k2_xboole_0 @ X9 @ k1_xboole_0 )
      = X9 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('23',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf(t127_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ) )).

thf('27',plain,(
    ! [X53: $i,X54: $i,X55: $i] :
      ( ( ( k8_relat_1 @ X53 @ ( k8_relat_1 @ X54 @ X55 ) )
        = ( k8_relat_1 @ ( k3_xboole_0 @ X53 @ X54 ) @ X55 ) )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t127_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ sk_A @ ( k8_relat_1 @ sk_B_1 @ X0 ) )
        = ( k8_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t123_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X49: $i,X50: $i] :
      ( ( ( k8_relat_1 @ X50 @ X49 )
        = ( k5_relat_1 @ X49 @ ( k6_relat_1 @ X50 ) ) )
      | ~ ( v1_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t123_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('30',plain,(
    ! [X56: $i,X57: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X56 @ ( k6_relat_1 @ X57 ) ) @ X56 )
      | ~ ( v1_relat_1 @ X56 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ X1 @ X0 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k8_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('34',plain,(
    ! [X51: $i,X52: $i] :
      ( ( ( k8_relat_1 @ X52 @ X51 )
        = ( k3_xboole_0 @ X51 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X51 ) @ X52 ) ) )
      | ~ ( v1_relat_1 @ X51 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X47 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k8_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k8_relat_1 @ sk_A @ X0 ) @ ( k8_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['33','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k8_relat_1 @ sk_A @ sk_C_1 ) @ ( k8_relat_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['42','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h4PwXZJpqJ
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 348 iterations in 0.120s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.58  thf(t79_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.21/0.58  thf('0', plain,
% 0.21/0.58      (![X18 : $i, X19 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X18 @ X19) @ X19)),
% 0.21/0.58      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.21/0.58  thf(symmetry_r1_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.58      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.21/0.58  thf('2', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.58  thf(t131_relat_1, conjecture,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ C ) =>
% 0.21/0.58       ( ( r1_tarski @ A @ B ) =>
% 0.21/0.58         ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.58        ( ( v1_relat_1 @ C ) =>
% 0.21/0.58          ( ( r1_tarski @ A @ B ) =>
% 0.21/0.58            ( r1_tarski @ ( k8_relat_1 @ A @ C ) @ ( k8_relat_1 @ B @ C ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t131_relat_1])).
% 0.21/0.58  thf('3', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t63_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.21/0.58       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.58         (~ (r1_tarski @ X15 @ X16)
% 0.21/0.58          | ~ (r1_xboole_0 @ X16 @ X17)
% 0.21/0.58          | (r1_xboole_0 @ X15 @ X17))),
% 0.21/0.58      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X0 : $i]: ((r1_xboole_0 @ sk_A @ X0) | ~ (r1_xboole_0 @ sk_B_1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      (![X0 : $i]: (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '5'])).
% 0.21/0.58  thf(t7_xboole_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.58          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.58  thf('7', plain,
% 0.21/0.58      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.21/0.58      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.58  thf(t4_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.58            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X4 @ (k3_xboole_0 @ X2 @ X5))
% 0.21/0.58          | ~ (r1_xboole_0 @ X2 @ X5))),
% 0.21/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.58  thf('9', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.58  thf(t47_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.58  thf('11', plain,
% 0.21/0.58      (![X10 : $i, X11 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11))
% 0.21/0.58           = (k4_xboole_0 @ X10 @ X11))),
% 0.21/0.58      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.21/0.58           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_1)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ sk_A @ k1_xboole_0)
% 0.21/0.58           = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_1)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf(t48_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.58  thf('14', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.58           = (k3_xboole_0 @ X12 @ X13))),
% 0.21/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_A @ k1_xboole_0))
% 0.21/0.58           = (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_1)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['13', '14'])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.58           = (k3_xboole_0 @ X12 @ X13))),
% 0.21/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_1)) = (k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['6', '9'])).
% 0.21/0.58  thf('18', plain, (((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.21/0.58  thf(t101_xboole_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( k5_xboole_0 @ A @ B ) =
% 0.21/0.58       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (![X7 : $i, X8 : $i]:
% 0.21/0.58         ((k5_xboole_0 @ X7 @ X8)
% 0.21/0.58           = (k4_xboole_0 @ (k2_xboole_0 @ X7 @ X8) @ (k3_xboole_0 @ X7 @ X8)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t101_xboole_1])).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (((k5_xboole_0 @ sk_A @ k1_xboole_0)
% 0.21/0.58         = (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ k1_xboole_0) @ k1_xboole_0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.58  thf(t5_boole, axiom,
% 0.21/0.58    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.58  thf('21', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.21/0.58      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.58  thf(t1_boole, axiom,
% 0.21/0.58    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.58  thf('22', plain, (![X9 : $i]: ((k2_xboole_0 @ X9 @ k1_xboole_0) = (X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [t1_boole])).
% 0.21/0.58  thf('23', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['12', '23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.58           = (k3_xboole_0 @ X12 @ X13))),
% 0.21/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.58  thf('26', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ sk_B_1))),
% 0.21/0.58      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.58  thf(t127_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ C ) =>
% 0.21/0.58       ( ( k8_relat_1 @ A @ ( k8_relat_1 @ B @ C ) ) =
% 0.21/0.58         ( k8_relat_1 @ ( k3_xboole_0 @ A @ B ) @ C ) ) ))).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (![X53 : $i, X54 : $i, X55 : $i]:
% 0.21/0.58         (((k8_relat_1 @ X53 @ (k8_relat_1 @ X54 @ X55))
% 0.21/0.58            = (k8_relat_1 @ (k3_xboole_0 @ X53 @ X54) @ X55))
% 0.21/0.58          | ~ (v1_relat_1 @ X55))),
% 0.21/0.58      inference('cnf', [status(esa)], [t127_relat_1])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k8_relat_1 @ sk_A @ (k8_relat_1 @ sk_B_1 @ X0))
% 0.21/0.58            = (k8_relat_1 @ sk_A @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['26', '27'])).
% 0.21/0.58  thf(t123_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ B ) =>
% 0.21/0.58       ( ( k8_relat_1 @ A @ B ) = ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) ) ))).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (![X49 : $i, X50 : $i]:
% 0.21/0.58         (((k8_relat_1 @ X50 @ X49) = (k5_relat_1 @ X49 @ (k6_relat_1 @ X50)))
% 0.21/0.58          | ~ (v1_relat_1 @ X49))),
% 0.21/0.58      inference('cnf', [status(esa)], [t123_relat_1])).
% 0.21/0.58  thf(t76_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ B ) =>
% 0.21/0.58       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.21/0.58         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (![X56 : $i, X57 : $i]:
% 0.21/0.58         ((r1_tarski @ (k5_relat_1 @ X56 @ (k6_relat_1 @ X57)) @ X56)
% 0.21/0.58          | ~ (v1_relat_1 @ X56))),
% 0.21/0.58      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['29', '30'])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0) | (r1_tarski @ (k8_relat_1 @ X1 @ X0) @ X0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['31'])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B_1 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ (k8_relat_1 @ sk_B_1 @ X0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['28', '32'])).
% 0.21/0.58  thf(t124_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ B ) =>
% 0.21/0.58       ( ( k8_relat_1 @ A @ B ) =
% 0.21/0.58         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      (![X51 : $i, X52 : $i]:
% 0.21/0.58         (((k8_relat_1 @ X52 @ X51)
% 0.21/0.58            = (k3_xboole_0 @ X51 @ (k2_zfmisc_1 @ (k1_relat_1 @ X51) @ X52)))
% 0.21/0.58          | ~ (v1_relat_1 @ X51))),
% 0.21/0.58      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (![X12 : $i, X13 : $i]:
% 0.21/0.58         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.21/0.58           = (k3_xboole_0 @ X12 @ X13))),
% 0.21/0.58      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.21/0.58  thf(fc2_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      (![X47 : $i, X48 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X47) | (v1_relat_1 @ (k4_xboole_0 @ X47 @ X48)))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)) | ~ (v1_relat_1 @ X1))),
% 0.21/0.58      inference('sup+', [status(thm)], ['35', '36'])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         ((v1_relat_1 @ (k8_relat_1 @ X1 @ X0))
% 0.21/0.58          | ~ (v1_relat_1 @ X0)
% 0.21/0.58          | ~ (v1_relat_1 @ X0))),
% 0.21/0.58      inference('sup+', [status(thm)], ['34', '37'])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k8_relat_1 @ X1 @ X0)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['38'])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X0)
% 0.21/0.58          | (r1_tarski @ (k8_relat_1 @ sk_A @ X0) @ (k8_relat_1 @ sk_B_1 @ X0)))),
% 0.21/0.58      inference('clc', [status(thm)], ['33', '39'])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (~ (r1_tarski @ (k8_relat_1 @ sk_A @ sk_C_1) @ 
% 0.21/0.58          (k8_relat_1 @ sk_B_1 @ sk_C_1))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('42', plain, (~ (v1_relat_1 @ sk_C_1)),
% 0.21/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.58  thf('43', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('44', plain, ($false), inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
