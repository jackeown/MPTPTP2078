%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FoKmnFndpV

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:05 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 147 expanded)
%              Number of leaves         :   28 (  56 expanded)
%              Depth                    :   14
%              Number of atoms          :  529 ( 978 expanded)
%              Number of equality atoms :   50 ( 102 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t46_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t46_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('1',plain,(
    ! [X43: $i,X45: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X43 ) @ X45 )
      | ~ ( r2_hidden @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ( X19 != X20 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('9',plain,(
    ! [X20: $i] :
      ( r1_tarski @ X20 @ X20 ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('14',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ( r2_hidden @ X13 @ X10 )
      | ( X12
       != ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( r2_hidden @ X13 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X13 @ X11 )
      | ( X12
       != ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ~ ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X13 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','21'])).

thf('23',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['6','22'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( X8
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X8 @ X5 @ X4 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X0 @ X1 ) @ X2 )
      | ( X2
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k2_tarski @ X32 @ X31 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X46: $i,X47: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X46 @ X47 ) )
      = ( k2_xboole_0 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('32',plain,(
    ! [X24: $i] :
      ( ( k2_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X29: $i,X30: $i] :
      ( r1_tarski @ X29 @ ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('35',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k3_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_tarski @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = X1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k4_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ k1_xboole_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('43',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ X7 @ X5 )
      | ( X6
       != ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('44',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( k1_xboole_0
        = ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','49'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('51',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_xboole_0 @ X27 @ ( k4_xboole_0 @ X28 @ X27 ) )
      = ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X24: $i] :
      ( ( k2_xboole_0 @ X24 @ k1_xboole_0 )
      = X24 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('54',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
 != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('57',plain,(
    ( k2_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) )
 != sk_B_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FoKmnFndpV
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.62/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.80  % Solved by: fo/fo7.sh
% 0.62/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.80  % done 957 iterations in 0.352s
% 0.62/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.80  % SZS output start Refutation
% 0.62/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.62/0.80  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.62/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.62/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.62/0.80  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.62/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.80  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.62/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.62/0.80  thf(sk_B_type, type, sk_B: $i > $i).
% 0.62/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.62/0.80  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.62/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.80  thf(t46_zfmisc_1, conjecture,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( r2_hidden @ A @ B ) =>
% 0.62/0.80       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.62/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.80    (~( ![A:$i,B:$i]:
% 0.62/0.80        ( ( r2_hidden @ A @ B ) =>
% 0.62/0.80          ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ) )),
% 0.62/0.80    inference('cnf.neg', [status(esa)], [t46_zfmisc_1])).
% 0.62/0.80  thf('0', plain, ((r2_hidden @ sk_A @ sk_B_1)),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf(l1_zfmisc_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.62/0.80  thf('1', plain,
% 0.62/0.80      (![X43 : $i, X45 : $i]:
% 0.62/0.80         ((r1_tarski @ (k1_tarski @ X43) @ X45) | ~ (r2_hidden @ X43 @ X45))),
% 0.62/0.80      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.62/0.80  thf('2', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B_1)),
% 0.62/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.62/0.80  thf(t28_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.62/0.80  thf('3', plain,
% 0.62/0.80      (![X25 : $i, X26 : $i]:
% 0.62/0.80         (((k3_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_tarski @ X25 @ X26))),
% 0.62/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.62/0.80  thf('4', plain,
% 0.62/0.80      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))),
% 0.62/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.62/0.80  thf(t100_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.62/0.80  thf('5', plain,
% 0.62/0.80      (![X22 : $i, X23 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X22 @ X23)
% 0.62/0.80           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.80  thf('6', plain,
% 0.62/0.80      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1)
% 0.62/0.80         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['4', '5'])).
% 0.62/0.80  thf(d1_xboole_0, axiom,
% 0.62/0.80    (![A:$i]:
% 0.62/0.80     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.62/0.80  thf('7', plain,
% 0.62/0.80      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.62/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.80  thf(d10_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.62/0.80  thf('8', plain,
% 0.62/0.80      (![X19 : $i, X20 : $i]: ((r1_tarski @ X19 @ X20) | ((X19) != (X20)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.62/0.80  thf('9', plain, (![X20 : $i]: (r1_tarski @ X20 @ X20)),
% 0.62/0.80      inference('simplify', [status(thm)], ['8'])).
% 0.62/0.80  thf('10', plain,
% 0.62/0.80      (![X25 : $i, X26 : $i]:
% 0.62/0.80         (((k3_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_tarski @ X25 @ X26))),
% 0.62/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.62/0.80  thf('11', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.80  thf('12', plain,
% 0.62/0.80      (![X22 : $i, X23 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X22 @ X23)
% 0.62/0.80           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.80  thf('13', plain,
% 0.62/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['11', '12'])).
% 0.62/0.80  thf(d5_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.62/0.80       ( ![D:$i]:
% 0.62/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.62/0.80           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.62/0.80  thf('14', plain,
% 0.62/0.80      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X13 @ X12)
% 0.62/0.80          | (r2_hidden @ X13 @ X10)
% 0.62/0.80          | ((X12) != (k4_xboole_0 @ X10 @ X11)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.62/0.80  thf('15', plain,
% 0.62/0.80      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.62/0.80         ((r2_hidden @ X13 @ X10)
% 0.62/0.80          | ~ (r2_hidden @ X13 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.62/0.80      inference('simplify', [status(thm)], ['14'])).
% 0.62/0.80  thf('16', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0)) | (r2_hidden @ X1 @ X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['13', '15'])).
% 0.62/0.80  thf('17', plain,
% 0.62/0.80      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['11', '12'])).
% 0.62/0.80  thf('18', plain,
% 0.62/0.80      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X13 @ X12)
% 0.62/0.80          | ~ (r2_hidden @ X13 @ X11)
% 0.62/0.80          | ((X12) != (k4_xboole_0 @ X10 @ X11)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.62/0.80  thf('19', plain,
% 0.62/0.80      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X13 @ X11)
% 0.62/0.80          | ~ (r2_hidden @ X13 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.62/0.80      inference('simplify', [status(thm)], ['18'])).
% 0.62/0.80  thf('20', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.62/0.80          | ~ (r2_hidden @ X1 @ X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['17', '19'])).
% 0.62/0.80  thf('21', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.62/0.80      inference('clc', [status(thm)], ['16', '20'])).
% 0.62/0.80  thf('22', plain, (![X0 : $i]: (v1_xboole_0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['7', '21'])).
% 0.62/0.80  thf('23', plain,
% 0.62/0.80      ((v1_xboole_0 @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.62/0.80      inference('sup+', [status(thm)], ['6', '22'])).
% 0.62/0.80  thf(d4_xboole_0, axiom,
% 0.62/0.80    (![A:$i,B:$i,C:$i]:
% 0.62/0.80     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.62/0.80       ( ![D:$i]:
% 0.62/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.62/0.80           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.62/0.80  thf('24', plain,
% 0.62/0.80      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.62/0.80         (((X8) = (k3_xboole_0 @ X4 @ X5))
% 0.62/0.80          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X5)
% 0.62/0.80          | (r2_hidden @ (sk_D @ X8 @ X5 @ X4) @ X8))),
% 0.62/0.80      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.62/0.80  thf('25', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.62/0.80      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.62/0.80  thf('26', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.62/0.80         ((r2_hidden @ (sk_D @ X2 @ X0 @ X1) @ X2)
% 0.62/0.80          | ((X2) = (k3_xboole_0 @ X1 @ X0))
% 0.62/0.80          | ~ (v1_xboole_0 @ X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['24', '25'])).
% 0.62/0.80  thf(commutativity_k2_tarski, axiom,
% 0.62/0.80    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.62/0.80  thf('27', plain,
% 0.62/0.80      (![X31 : $i, X32 : $i]:
% 0.62/0.80         ((k2_tarski @ X32 @ X31) = (k2_tarski @ X31 @ X32))),
% 0.62/0.80      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.62/0.80  thf(l51_zfmisc_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.62/0.80  thf('28', plain,
% 0.62/0.80      (![X46 : $i, X47 : $i]:
% 0.62/0.80         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.62/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.62/0.80  thf('29', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('sup+', [status(thm)], ['27', '28'])).
% 0.62/0.80  thf('30', plain,
% 0.62/0.80      (![X46 : $i, X47 : $i]:
% 0.62/0.80         ((k3_tarski @ (k2_tarski @ X46 @ X47)) = (k2_xboole_0 @ X46 @ X47))),
% 0.62/0.80      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.62/0.80  thf('31', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('sup+', [status(thm)], ['29', '30'])).
% 0.62/0.80  thf(t1_boole, axiom,
% 0.62/0.80    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.62/0.80  thf('32', plain, (![X24 : $i]: ((k2_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 0.62/0.80      inference('cnf', [status(esa)], [t1_boole])).
% 0.62/0.80  thf('33', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['31', '32'])).
% 0.62/0.80  thf(t7_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.62/0.80  thf('34', plain,
% 0.62/0.80      (![X29 : $i, X30 : $i]: (r1_tarski @ X29 @ (k2_xboole_0 @ X29 @ X30))),
% 0.62/0.80      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.62/0.80  thf('35', plain,
% 0.62/0.80      (![X25 : $i, X26 : $i]:
% 0.62/0.80         (((k3_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_tarski @ X25 @ X26))),
% 0.62/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.62/0.80  thf('36', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         ((k3_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (X1))),
% 0.62/0.80      inference('sup-', [status(thm)], ['34', '35'])).
% 0.62/0.80  thf('37', plain,
% 0.62/0.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['33', '36'])).
% 0.62/0.80  thf('38', plain,
% 0.62/0.80      (![X22 : $i, X23 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ X22 @ X23)
% 0.62/0.80           = (k5_xboole_0 @ X22 @ (k3_xboole_0 @ X22 @ X23)))),
% 0.62/0.80      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.62/0.80  thf('39', plain,
% 0.62/0.80      (![X0 : $i]:
% 0.62/0.80         ((k4_xboole_0 @ k1_xboole_0 @ X0)
% 0.62/0.80           = (k5_xboole_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['37', '38'])).
% 0.62/0.80  thf('40', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.62/0.80          | ~ (r2_hidden @ X1 @ X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['17', '19'])).
% 0.62/0.80  thf('41', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X1 @ (k4_xboole_0 @ k1_xboole_0 @ X0))
% 0.62/0.80          | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['39', '40'])).
% 0.62/0.80  thf('42', plain,
% 0.62/0.80      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['33', '36'])).
% 0.62/0.80  thf('43', plain,
% 0.62/0.80      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X7 @ X6)
% 0.62/0.80          | (r2_hidden @ X7 @ X5)
% 0.62/0.80          | ((X6) != (k3_xboole_0 @ X4 @ X5)))),
% 0.62/0.80      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.62/0.80  thf('44', plain,
% 0.62/0.80      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.62/0.80         ((r2_hidden @ X7 @ X5) | ~ (r2_hidden @ X7 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.62/0.80      inference('simplify', [status(thm)], ['43'])).
% 0.62/0.80  thf('45', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (r2_hidden @ X1 @ k1_xboole_0) | (r2_hidden @ X1 @ X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['42', '44'])).
% 0.62/0.80  thf('46', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.62/0.80      inference('clc', [status(thm)], ['41', '45'])).
% 0.62/0.80  thf('47', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]:
% 0.62/0.80         (~ (v1_xboole_0 @ X1) | ((k1_xboole_0) = (k3_xboole_0 @ X0 @ X1)))),
% 0.62/0.80      inference('sup-', [status(thm)], ['26', '46'])).
% 0.62/0.80  thf('48', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.62/0.80      inference('sup-', [status(thm)], ['9', '10'])).
% 0.62/0.80  thf('49', plain,
% 0.62/0.80      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.62/0.80      inference('sup+', [status(thm)], ['47', '48'])).
% 0.62/0.80  thf('50', plain,
% 0.62/0.80      (((k1_xboole_0) = (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))),
% 0.62/0.80      inference('sup-', [status(thm)], ['23', '49'])).
% 0.62/0.80  thf(t39_xboole_1, axiom,
% 0.62/0.80    (![A:$i,B:$i]:
% 0.62/0.80     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.62/0.80  thf('51', plain,
% 0.62/0.80      (![X27 : $i, X28 : $i]:
% 0.62/0.80         ((k2_xboole_0 @ X27 @ (k4_xboole_0 @ X28 @ X27))
% 0.62/0.80           = (k2_xboole_0 @ X27 @ X28))),
% 0.62/0.80      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.62/0.80  thf('52', plain,
% 0.62/0.80      (((k2_xboole_0 @ sk_B_1 @ k1_xboole_0)
% 0.62/0.80         = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.62/0.80      inference('sup+', [status(thm)], ['50', '51'])).
% 0.62/0.80  thf('53', plain, (![X24 : $i]: ((k2_xboole_0 @ X24 @ k1_xboole_0) = (X24))),
% 0.62/0.80      inference('cnf', [status(esa)], [t1_boole])).
% 0.62/0.80  thf('54', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))),
% 0.62/0.80      inference('demod', [status(thm)], ['52', '53'])).
% 0.62/0.80  thf('55', plain, (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (sk_B_1))),
% 0.62/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.80  thf('56', plain,
% 0.62/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.62/0.80      inference('sup+', [status(thm)], ['29', '30'])).
% 0.62/0.80  thf('57', plain, (((k2_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)) != (sk_B_1))),
% 0.62/0.80      inference('demod', [status(thm)], ['55', '56'])).
% 0.62/0.80  thf('58', plain, ($false),
% 0.62/0.80      inference('simplify_reflect-', [status(thm)], ['54', '57'])).
% 0.62/0.80  
% 0.62/0.80  % SZS output end Refutation
% 0.62/0.80  
% 0.62/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
