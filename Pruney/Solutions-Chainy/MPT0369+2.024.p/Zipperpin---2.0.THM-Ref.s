%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7yvSuU13X

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:17 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 112 expanded)
%              Number of leaves         :   30 (  45 expanded)
%              Depth                    :   16
%              Number of atoms          :  501 ( 816 expanded)
%              Number of equality atoms :   40 (  58 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t50_subset_1,conjecture,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ( ~ ( r2_hidden @ C @ B )
               => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ~ ( r2_hidden @ C @ B )
                 => ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_subset_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_subset_1 @ X24 @ X25 )
        = ( k4_xboole_0 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('2',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X4 @ X5 ) @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('4',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_A ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,
    ( ( r1_tarski @ sk_B @ sk_A )
    | ( r1_tarski @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('26',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['16','24','27'])).

thf('29',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['4','28'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('30',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t45_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( B
        = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ) )).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X18
        = ( k2_xboole_0 @ X17 @ ( k4_xboole_0 @ X18 @ X17 ) ) )
      | ~ ( r1_tarski @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t45_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('33',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('36',plain,(
    ! [X19: $i] :
      ( ( k5_xboole_0 @ X19 @ k1_xboole_0 )
      = X19 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','37'])).

thf('39',plain,
    ( ( k5_xboole_0 @ sk_B @ sk_A )
    = ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['29','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('41',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ X22 )
      | ( r2_hidden @ X21 @ X22 )
      | ( v1_xboole_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('43',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k5_xboole_0 @ X8 @ X10 ) )
      | ( r2_hidden @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ sk_C_1 @ X0 )
      | ( r2_hidden @ sk_C_1 @ ( k5_xboole_0 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['39','44'])).

thf('46',plain,(
    ~ ( r2_hidden @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( r2_hidden @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['47','48'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('50',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a7yvSuU13X
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:04:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.57  % Solved by: fo/fo7.sh
% 0.37/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.57  % done 175 iterations in 0.107s
% 0.37/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.57  % SZS output start Refutation
% 0.37/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.37/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.57  thf(t50_subset_1, conjecture,
% 0.37/0.57    (![A:$i]:
% 0.37/0.57     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.37/0.57       ( ![B:$i]:
% 0.37/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57           ( ![C:$i]:
% 0.37/0.57             ( ( m1_subset_1 @ C @ A ) =>
% 0.37/0.57               ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.37/0.57                 ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ))).
% 0.37/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.57    (~( ![A:$i]:
% 0.37/0.57        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.37/0.57          ( ![B:$i]:
% 0.37/0.57            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57              ( ![C:$i]:
% 0.37/0.57                ( ( m1_subset_1 @ C @ A ) =>
% 0.37/0.57                  ( ( ~( r2_hidden @ C @ B ) ) =>
% 0.37/0.57                    ( r2_hidden @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) ) ) )),
% 0.37/0.57    inference('cnf.neg', [status(esa)], [t50_subset_1])).
% 0.37/0.57  thf('0', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(d5_subset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.57  thf('1', plain,
% 0.37/0.57      (![X24 : $i, X25 : $i]:
% 0.37/0.57         (((k3_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))
% 0.37/0.57          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X24)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.57  thf('2', plain,
% 0.37/0.57      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.57  thf(d6_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k5_xboole_0 @ A @ B ) =
% 0.37/0.57       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.37/0.57  thf('3', plain,
% 0.37/0.57      (![X4 : $i, X5 : $i]:
% 0.37/0.57         ((k5_xboole_0 @ X4 @ X5)
% 0.37/0.57           = (k2_xboole_0 @ (k4_xboole_0 @ X4 @ X5) @ (k4_xboole_0 @ X5 @ X4)))),
% 0.37/0.57      inference('cnf', [status(esa)], [d6_xboole_0])).
% 0.37/0.57  thf('4', plain,
% 0.37/0.57      (((k5_xboole_0 @ sk_B @ sk_A)
% 0.37/0.57         = (k2_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_A) @ 
% 0.37/0.57            (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('sup+', [status(thm)], ['2', '3'])).
% 0.37/0.57  thf(d3_tarski, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.57  thf('5', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('6', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(l3_subset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.37/0.57  thf('7', plain,
% 0.37/0.57      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.37/0.57         (~ (r2_hidden @ X26 @ X27)
% 0.37/0.57          | (r2_hidden @ X26 @ X28)
% 0.37/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28)))),
% 0.37/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.37/0.57  thf('8', plain,
% 0.37/0.57      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.57  thf('9', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((r1_tarski @ sk_B @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.37/0.57  thf('10', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('11', plain, (((r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['9', '10'])).
% 0.37/0.57  thf('12', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.37/0.57      inference('simplify', [status(thm)], ['11'])).
% 0.37/0.57  thf(t28_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.57  thf('13', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.57  thf('14', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 0.37/0.57      inference('sup-', [status(thm)], ['12', '13'])).
% 0.37/0.57  thf(t100_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.37/0.57  thf('15', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X11 @ X12)
% 0.37/0.57           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('16', plain,
% 0.37/0.57      (((k4_xboole_0 @ sk_B @ sk_A) = (k5_xboole_0 @ sk_B @ sk_B))),
% 0.37/0.57      inference('sup+', [status(thm)], ['14', '15'])).
% 0.37/0.57  thf('17', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('18', plain,
% 0.37/0.57      (![X1 : $i, X3 : $i]:
% 0.37/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.37/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.57  thf('19', plain,
% 0.37/0.57      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['17', '18'])).
% 0.37/0.57  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.37/0.57      inference('simplify', [status(thm)], ['19'])).
% 0.37/0.57  thf('21', plain,
% 0.37/0.57      (![X13 : $i, X14 : $i]:
% 0.37/0.57         (((k3_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_tarski @ X13 @ X14))),
% 0.37/0.57      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.37/0.57  thf('22', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.57  thf('23', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X11 @ X12)
% 0.37/0.57           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('24', plain,
% 0.37/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf('25', plain,
% 0.37/0.57      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.57  thf(t92_xboole_1, axiom,
% 0.37/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.37/0.57  thf('26', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.37/0.57  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['25', '26'])).
% 0.37/0.57  thf('28', plain, (((k4_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.37/0.57      inference('demod', [status(thm)], ['16', '24', '27'])).
% 0.37/0.57  thf('29', plain,
% 0.37/0.57      (((k5_xboole_0 @ sk_B @ sk_A)
% 0.37/0.57         = (k2_xboole_0 @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B)))),
% 0.37/0.57      inference('demod', [status(thm)], ['4', '28'])).
% 0.37/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.57  thf('30', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.57  thf(t45_xboole_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( r1_tarski @ A @ B ) =>
% 0.37/0.57       ( ( B ) = ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) ))).
% 0.37/0.57  thf('31', plain,
% 0.37/0.57      (![X17 : $i, X18 : $i]:
% 0.37/0.57         (((X18) = (k2_xboole_0 @ X17 @ (k4_xboole_0 @ X18 @ X17)))
% 0.37/0.57          | ~ (r1_tarski @ X17 @ X18))),
% 0.37/0.57      inference('cnf', [status(esa)], [t45_xboole_1])).
% 0.37/0.57  thf('32', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((X0) = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.57  thf(t2_boole, axiom,
% 0.37/0.57    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.57  thf('33', plain,
% 0.37/0.57      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [t2_boole])).
% 0.37/0.57  thf('34', plain,
% 0.37/0.57      (![X11 : $i, X12 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X11 @ X12)
% 0.37/0.57           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.37/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.37/0.57  thf('35', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['33', '34'])).
% 0.37/0.57  thf(t5_boole, axiom,
% 0.37/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.37/0.57  thf('36', plain, (![X19 : $i]: ((k5_xboole_0 @ X19 @ k1_xboole_0) = (X19))),
% 0.37/0.57      inference('cnf', [status(esa)], [t5_boole])).
% 0.37/0.57  thf('37', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.37/0.57      inference('sup+', [status(thm)], ['35', '36'])).
% 0.37/0.57  thf('38', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.37/0.57      inference('demod', [status(thm)], ['32', '37'])).
% 0.37/0.57  thf('39', plain,
% 0.37/0.57      (((k5_xboole_0 @ sk_B @ sk_A) = (k3_subset_1 @ sk_A @ sk_B))),
% 0.37/0.57      inference('demod', [status(thm)], ['29', '38'])).
% 0.37/0.57  thf('40', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf(d2_subset_1, axiom,
% 0.37/0.57    (![A:$i,B:$i]:
% 0.37/0.57     ( ( ( v1_xboole_0 @ A ) =>
% 0.37/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.37/0.57       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.37/0.57         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.57  thf('41', plain,
% 0.37/0.57      (![X21 : $i, X22 : $i]:
% 0.37/0.57         (~ (m1_subset_1 @ X21 @ X22)
% 0.37/0.57          | (r2_hidden @ X21 @ X22)
% 0.37/0.57          | (v1_xboole_0 @ X22))),
% 0.37/0.57      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.37/0.57  thf('42', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C_1 @ sk_A))),
% 0.37/0.57      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.57  thf(t1_xboole_0, axiom,
% 0.37/0.57    (![A:$i,B:$i,C:$i]:
% 0.37/0.57     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.37/0.57       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.37/0.57  thf('43', plain,
% 0.37/0.57      (![X7 : $i, X8 : $i, X10 : $i]:
% 0.37/0.57         ((r2_hidden @ X7 @ (k5_xboole_0 @ X8 @ X10))
% 0.37/0.57          | (r2_hidden @ X7 @ X8)
% 0.37/0.57          | ~ (r2_hidden @ X7 @ X10))),
% 0.37/0.57      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.37/0.57  thf('44', plain,
% 0.37/0.57      (![X0 : $i]:
% 0.37/0.57         ((v1_xboole_0 @ sk_A)
% 0.37/0.57          | (r2_hidden @ sk_C_1 @ X0)
% 0.37/0.57          | (r2_hidden @ sk_C_1 @ (k5_xboole_0 @ X0 @ sk_A)))),
% 0.37/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.37/0.57  thf('45', plain,
% 0.37/0.57      (((r2_hidden @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.37/0.57        | (r2_hidden @ sk_C_1 @ sk_B)
% 0.37/0.57        | (v1_xboole_0 @ sk_A))),
% 0.37/0.57      inference('sup+', [status(thm)], ['39', '44'])).
% 0.37/0.57  thf('46', plain, (~ (r2_hidden @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('47', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C_1 @ sk_B))),
% 0.37/0.57      inference('clc', [status(thm)], ['45', '46'])).
% 0.37/0.57  thf('48', plain, (~ (r2_hidden @ sk_C_1 @ sk_B)),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('49', plain, ((v1_xboole_0 @ sk_A)),
% 0.37/0.57      inference('clc', [status(thm)], ['47', '48'])).
% 0.37/0.57  thf(l13_xboole_0, axiom,
% 0.37/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.57  thf('50', plain,
% 0.37/0.57      (![X6 : $i]: (((X6) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X6))),
% 0.37/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.57  thf('51', plain, (((sk_A) = (k1_xboole_0))),
% 0.37/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.37/0.57  thf('52', plain, (((sk_A) != (k1_xboole_0))),
% 0.37/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.57  thf('53', plain, ($false),
% 0.37/0.57      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.37/0.57  
% 0.37/0.57  % SZS output end Refutation
% 0.37/0.57  
% 0.37/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
