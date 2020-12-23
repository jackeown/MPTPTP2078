%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CKbhYV5I1B

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 164 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  525 (1319 expanded)
%              Number of equality atoms :   42 ( 109 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,
    ( ( r1_tarski @ sk_B_2 @ sk_A )
    | ( r1_tarski @ sk_B_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_tarski @ sk_B_2 @ sk_A ),
    inference(simplify,[status(thm)],['7'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k3_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_B_2 @ sk_A )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B_2 )
    = sk_B_2 ),
    inference(demod,[status(thm)],['10','11'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B_2 )
    = ( k5_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_B_2
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
   <= ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( r1_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
        | ~ ( r2_hidden @ X0 @ sk_B_2 ) )
   <= ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_B_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('23',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_2 )
    = ( k4_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B_2 ) )
        | ~ ( r2_hidden @ X0 @ sk_B_2 ) )
   <= ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,
    ( ( sk_B_2
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( sk_B_2
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    ! [X6: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X8 )
      | ( r2_hidden @ ( sk_C @ X8 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('29',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('34',plain,(
    ! [X19: $i] :
      ( ( k1_subset_1 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('35',plain,
    ( ( sk_B_2
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_2
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('36',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_2 )
    = ( k4_xboole_0 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
   <= ~ ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_B_2 @ ( k4_xboole_0 @ sk_A @ sk_B_2 ) )
   <= ~ ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ sk_B_2 ) )
   <= ( ~ ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
      & ( sk_B_2
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,
    ( ( sk_B_2 = k1_xboole_0 )
   <= ( sk_B_2
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('42',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_xboole_0 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
      & ( sk_B_2
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
    | ( sk_B_2
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','42'])).

thf('44',plain,
    ( ( r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) )
    | ( sk_B_2
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['17'])).

thf('45',plain,(
    r1_tarski @ sk_B_2 @ ( k3_subset_1 @ sk_A @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['26','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['24','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference(clc,[status(thm)],['16','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_2 ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    sk_B_2 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,
    ( ( sk_B_2
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_2
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['25'])).

thf('52',plain,(
    ! [X19: $i] :
      ( ( k1_subset_1 @ X19 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('53',plain,
    ( ( sk_B_2 != k1_xboole_0 )
   <= ( sk_B_2
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    sk_B_2
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['26','43'])).

thf('55',plain,(
    sk_B_2 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['53','54'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CKbhYV5I1B
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:51:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 194 iterations in 0.065s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.20/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.20/0.52  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.52  thf(t7_xboole_0, axiom,
% 0.20/0.52    (![A:$i]:
% 0.20/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.20/0.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X13 : $i]:
% 0.20/0.52         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 0.20/0.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.20/0.52  thf(d3_tarski, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.52  thf('1', plain,
% 0.20/0.52      (![X6 : $i, X8 : $i]:
% 0.20/0.52         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf(t38_subset_1, conjecture,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.52         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i]:
% 0.20/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.20/0.52            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.20/0.52    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.20/0.52  thf('2', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(l3_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.52  thf('3', plain,
% 0.20/0.52      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X22 @ X23)
% 0.20/0.52          | (r2_hidden @ X22 @ X24)
% 0.20/0.52          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.20/0.52      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.52  thf('4', plain,
% 0.20/0.52      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('5', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r1_tarski @ sk_B_2 @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_B_2) @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.52  thf('6', plain,
% 0.20/0.52      (![X6 : $i, X8 : $i]:
% 0.20/0.52         ((r1_tarski @ X6 @ X8) | ~ (r2_hidden @ (sk_C @ X8 @ X6) @ X8))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('7', plain,
% 0.20/0.52      (((r1_tarski @ sk_B_2 @ sk_A) | (r1_tarski @ sk_B_2 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.52  thf('8', plain, ((r1_tarski @ sk_B_2 @ sk_A)),
% 0.20/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.52  thf(t28_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.52  thf('9', plain,
% 0.20/0.52      (![X16 : $i, X17 : $i]:
% 0.20/0.52         (((k3_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_tarski @ X16 @ X17))),
% 0.20/0.52      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.20/0.52  thf('10', plain, (((k3_xboole_0 @ sk_B_2 @ sk_A) = (sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.52  thf('11', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.52  thf('12', plain, (((k3_xboole_0 @ sk_A @ sk_B_2) = (sk_B_2))),
% 0.20/0.52      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.52  thf(t100_xboole_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('13', plain,
% 0.20/0.52      (![X14 : $i, X15 : $i]:
% 0.20/0.52         ((k4_xboole_0 @ X14 @ X15)
% 0.20/0.52           = (k5_xboole_0 @ X14 @ (k3_xboole_0 @ X14 @ X15)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.52  thf('14', plain,
% 0.20/0.52      (((k4_xboole_0 @ sk_A @ sk_B_2) = (k5_xboole_0 @ sk_A @ sk_B_2))),
% 0.20/0.52      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.52  thf(t1_xboole_0, axiom,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.20/0.52       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.20/0.52  thf('15', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.52          | ~ (r2_hidden @ X9 @ X11)
% 0.20/0.52          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.52  thf('16', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B_2))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B_2)
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.52      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.52  thf('17', plain,
% 0.20/0.52      ((((sk_B_2) = (k1_subset_1 @ sk_A))
% 0.20/0.52        | (r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('18', plain,
% 0.20/0.52      (((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2)))
% 0.20/0.52         <= (((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))))),
% 0.20/0.52      inference('split', [status(esa)], ['17'])).
% 0.20/0.52  thf('19', plain,
% 0.20/0.52      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.52          | (r2_hidden @ X5 @ X7)
% 0.20/0.52          | ~ (r1_tarski @ X6 @ X7))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf('20', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_2))
% 0.20/0.52           | ~ (r2_hidden @ X0 @ sk_B_2)))
% 0.20/0.52         <= (((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.52  thf('21', plain, ((m1_subset_1 @ sk_B_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf(d5_subset_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.52       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.52  thf('22', plain,
% 0.20/0.52      (![X20 : $i, X21 : $i]:
% 0.20/0.52         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.20/0.52          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.20/0.52      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.52  thf('23', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B_2) = (k4_xboole_0 @ sk_A @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('24', plain,
% 0.20/0.52      ((![X0 : $i]:
% 0.20/0.52          ((r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B_2))
% 0.20/0.52           | ~ (r2_hidden @ X0 @ sk_B_2)))
% 0.20/0.52         <= (((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))))),
% 0.20/0.52      inference('demod', [status(thm)], ['20', '23'])).
% 0.20/0.52  thf('25', plain,
% 0.20/0.52      ((((sk_B_2) != (k1_subset_1 @ sk_A))
% 0.20/0.52        | ~ (r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2)))),
% 0.20/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.52  thf('26', plain,
% 0.20/0.52      (~ (((sk_B_2) = (k1_subset_1 @ sk_A))) | 
% 0.20/0.52       ~ ((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2)))),
% 0.20/0.52      inference('split', [status(esa)], ['25'])).
% 0.20/0.52  thf('27', plain,
% 0.20/0.52      (![X6 : $i, X8 : $i]:
% 0.20/0.52         ((r1_tarski @ X6 @ X8) | (r2_hidden @ (sk_C @ X8 @ X6) @ X6))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.52  thf(t92_xboole_1, axiom,
% 0.20/0.52    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('28', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.52  thf('29', plain,
% 0.20/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X9 @ X10)
% 0.20/0.52          | ~ (r2_hidden @ X9 @ X11)
% 0.20/0.52          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 0.20/0.52      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.20/0.52  thf('30', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 0.20/0.52          | ~ (r2_hidden @ X1 @ X0)
% 0.20/0.52          | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.52  thf('31', plain,
% 0.20/0.52      (![X0 : $i, X1 : $i]:
% 0.20/0.52         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.20/0.52      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.52  thf('32', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.52      inference('condensation', [status(thm)], ['31'])).
% 0.20/0.52  thf('33', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.52      inference('sup-', [status(thm)], ['27', '32'])).
% 0.20/0.52  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.52  thf('34', plain, (![X19 : $i]: ((k1_subset_1 @ X19) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.52  thf('35', plain,
% 0.20/0.52      ((((sk_B_2) = (k1_subset_1 @ sk_A)))
% 0.20/0.52         <= ((((sk_B_2) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('split', [status(esa)], ['17'])).
% 0.20/0.52  thf('36', plain,
% 0.20/0.52      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('37', plain,
% 0.20/0.52      (((k3_subset_1 @ sk_A @ sk_B_2) = (k4_xboole_0 @ sk_A @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.52  thf('38', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2)))
% 0.20/0.52         <= (~ ((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))))),
% 0.20/0.52      inference('split', [status(esa)], ['25'])).
% 0.20/0.52  thf('39', plain,
% 0.20/0.52      ((~ (r1_tarski @ sk_B_2 @ (k4_xboole_0 @ sk_A @ sk_B_2)))
% 0.20/0.52         <= (~ ((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.52  thf('40', plain,
% 0.20/0.52      ((~ (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ sk_B_2)))
% 0.20/0.52         <= (~ ((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))) & 
% 0.20/0.52             (((sk_B_2) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('sup-', [status(thm)], ['36', '39'])).
% 0.20/0.52  thf('41', plain,
% 0.20/0.52      ((((sk_B_2) = (k1_xboole_0))) <= ((((sk_B_2) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('sup+', [status(thm)], ['34', '35'])).
% 0.20/0.52  thf('42', plain,
% 0.20/0.52      ((~ (r1_tarski @ k1_xboole_0 @ (k4_xboole_0 @ sk_A @ k1_xboole_0)))
% 0.20/0.52         <= (~ ((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))) & 
% 0.20/0.52             (((sk_B_2) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.52  thf('43', plain,
% 0.20/0.52      (((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))) | 
% 0.20/0.52       ~ (((sk_B_2) = (k1_subset_1 @ sk_A)))),
% 0.20/0.52      inference('sup-', [status(thm)], ['33', '42'])).
% 0.20/0.52  thf('44', plain,
% 0.20/0.52      (((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2))) | 
% 0.20/0.52       (((sk_B_2) = (k1_subset_1 @ sk_A)))),
% 0.20/0.52      inference('split', [status(esa)], ['17'])).
% 0.20/0.52  thf('45', plain, (((r1_tarski @ sk_B_2 @ (k3_subset_1 @ sk_A @ sk_B_2)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['26', '43', '44'])).
% 0.20/0.52  thf('46', plain,
% 0.20/0.52      (![X0 : $i]:
% 0.20/0.52         ((r2_hidden @ X0 @ (k4_xboole_0 @ sk_A @ sk_B_2))
% 0.20/0.52          | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['24', '45'])).
% 0.20/0.52  thf('47', plain,
% 0.20/0.52      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.20/0.52      inference('clc', [status(thm)], ['16', '46'])).
% 0.20/0.52  thf('48', plain,
% 0.20/0.52      (![X0 : $i]: ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_B_2))),
% 0.20/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.52  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_B_2)),
% 0.20/0.52      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.52  thf('50', plain, (((sk_B_2) = (k1_xboole_0))),
% 0.20/0.52      inference('sup-', [status(thm)], ['0', '49'])).
% 0.20/0.52  thf('51', plain,
% 0.20/0.52      ((((sk_B_2) != (k1_subset_1 @ sk_A)))
% 0.20/0.52         <= (~ (((sk_B_2) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('split', [status(esa)], ['25'])).
% 0.20/0.52  thf('52', plain, (![X19 : $i]: ((k1_subset_1 @ X19) = (k1_xboole_0))),
% 0.20/0.52      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.52  thf('53', plain,
% 0.20/0.52      ((((sk_B_2) != (k1_xboole_0))) <= (~ (((sk_B_2) = (k1_subset_1 @ sk_A))))),
% 0.20/0.52      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.52  thf('54', plain, (~ (((sk_B_2) = (k1_subset_1 @ sk_A)))),
% 0.20/0.52      inference('sat_resolution*', [status(thm)], ['26', '43'])).
% 0.20/0.52  thf('55', plain, (((sk_B_2) != (k1_xboole_0))),
% 0.20/0.52      inference('simpl_trail', [status(thm)], ['53', '54'])).
% 0.20/0.52  thf('56', plain, ($false),
% 0.20/0.52      inference('simplify_reflect-', [status(thm)], ['50', '55'])).
% 0.20/0.52  
% 0.20/0.52  % SZS output end Refutation
% 0.20/0.52  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
