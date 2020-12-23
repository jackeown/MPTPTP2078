%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mYoUe64cAB

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:11 EST 2020

% Result     : Theorem 4.11s
% Output     : Refutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 106 expanded)
%              Number of leaves         :   26 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  562 (1025 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t31_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_tarski @ B @ C )
            <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ ( k4_xboole_0 @ X16 @ X15 ) @ ( k4_xboole_0 @ X16 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X34 @ X35 )
        = ( k4_xboole_0 @ X34 @ X35 ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('12',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('15',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('18',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t51_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) )
      = A ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X17 @ X18 ) @ ( k4_xboole_0 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[t51_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_xboole_0 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('34',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ X32 )
      | ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('36',plain,(
    ! [X36: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('37',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['35','36'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( r1_tarski @ X27 @ X25 )
      | ( X26
       != ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('39',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','40'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ~ ( r1_tarski @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) @ X0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','43'])).

thf('45',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mYoUe64cAB
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.11/4.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.11/4.31  % Solved by: fo/fo7.sh
% 4.11/4.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.11/4.31  % done 4942 iterations in 3.857s
% 4.11/4.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.11/4.31  % SZS output start Refutation
% 4.11/4.31  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.11/4.31  thf(sk_C_1_type, type, sk_C_1: $i).
% 4.11/4.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.11/4.31  thf(sk_B_type, type, sk_B: $i).
% 4.11/4.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.11/4.31  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.11/4.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.11/4.31  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.11/4.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.11/4.31  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 4.11/4.31  thf(sk_A_type, type, sk_A: $i).
% 4.11/4.31  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.11/4.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.11/4.31  thf(t31_subset_1, conjecture,
% 4.11/4.31    (![A:$i,B:$i]:
% 4.11/4.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.11/4.31       ( ![C:$i]:
% 4.11/4.31         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.11/4.31           ( ( r1_tarski @ B @ C ) <=>
% 4.11/4.31             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 4.11/4.31  thf(zf_stmt_0, negated_conjecture,
% 4.11/4.31    (~( ![A:$i,B:$i]:
% 4.11/4.31        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.11/4.31          ( ![C:$i]:
% 4.11/4.31            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 4.11/4.31              ( ( r1_tarski @ B @ C ) <=>
% 4.11/4.31                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 4.11/4.31    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 4.11/4.31  thf('0', plain,
% 4.11/4.31      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31           (k3_subset_1 @ sk_A @ sk_B))
% 4.11/4.31        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 4.11/4.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.11/4.31  thf('1', plain,
% 4.11/4.31      (~
% 4.11/4.31       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31         (k3_subset_1 @ sk_A @ sk_B))) | 
% 4.11/4.31       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 4.11/4.31      inference('split', [status(esa)], ['0'])).
% 4.11/4.31  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 4.11/4.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.11/4.31  thf(d5_subset_1, axiom,
% 4.11/4.31    (![A:$i,B:$i]:
% 4.11/4.31     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 4.11/4.31       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 4.11/4.31  thf('3', plain,
% 4.11/4.31      (![X34 : $i, X35 : $i]:
% 4.11/4.31         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 4.11/4.31          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 4.11/4.31      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.11/4.31  thf('4', plain,
% 4.11/4.31      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 4.11/4.31      inference('sup-', [status(thm)], ['2', '3'])).
% 4.11/4.31  thf('5', plain,
% 4.11/4.31      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31         (k3_subset_1 @ sk_A @ sk_B))
% 4.11/4.31        | (r1_tarski @ sk_B @ sk_C_1))),
% 4.11/4.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.11/4.31  thf('6', plain,
% 4.11/4.31      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 4.11/4.31      inference('split', [status(esa)], ['5'])).
% 4.11/4.31  thf(t34_xboole_1, axiom,
% 4.11/4.31    (![A:$i,B:$i,C:$i]:
% 4.11/4.31     ( ( r1_tarski @ A @ B ) =>
% 4.11/4.31       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 4.11/4.31  thf('7', plain,
% 4.11/4.31      (![X14 : $i, X15 : $i, X16 : $i]:
% 4.11/4.31         (~ (r1_tarski @ X14 @ X15)
% 4.11/4.31          | (r1_tarski @ (k4_xboole_0 @ X16 @ X15) @ (k4_xboole_0 @ X16 @ X14)))),
% 4.11/4.31      inference('cnf', [status(esa)], [t34_xboole_1])).
% 4.11/4.31  thf('8', plain,
% 4.11/4.31      ((![X0 : $i]:
% 4.11/4.31          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 4.11/4.31         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 4.11/4.31      inference('sup-', [status(thm)], ['6', '7'])).
% 4.11/4.31  thf('9', plain,
% 4.11/4.31      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 4.11/4.31      inference('sup+', [status(thm)], ['4', '8'])).
% 4.11/4.31  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.11/4.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.11/4.31  thf('11', plain,
% 4.11/4.31      (![X34 : $i, X35 : $i]:
% 4.11/4.31         (((k3_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))
% 4.11/4.31          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X34)))),
% 4.11/4.31      inference('cnf', [status(esa)], [d5_subset_1])).
% 4.11/4.31  thf('12', plain,
% 4.11/4.31      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 4.11/4.31      inference('sup-', [status(thm)], ['10', '11'])).
% 4.11/4.31  thf('13', plain,
% 4.11/4.31      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 4.11/4.31      inference('demod', [status(thm)], ['9', '12'])).
% 4.11/4.31  thf('14', plain,
% 4.11/4.31      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31           (k3_subset_1 @ sk_A @ sk_B)))
% 4.11/4.31         <= (~
% 4.11/4.31             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31               (k3_subset_1 @ sk_A @ sk_B))))),
% 4.11/4.31      inference('split', [status(esa)], ['0'])).
% 4.11/4.31  thf('15', plain,
% 4.11/4.31      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31         (k3_subset_1 @ sk_A @ sk_B))) | 
% 4.11/4.31       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 4.11/4.31      inference('sup-', [status(thm)], ['13', '14'])).
% 4.11/4.31  thf('16', plain,
% 4.11/4.31      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31         (k3_subset_1 @ sk_A @ sk_B))) | 
% 4.11/4.31       ((r1_tarski @ sk_B @ sk_C_1))),
% 4.11/4.31      inference('split', [status(esa)], ['5'])).
% 4.11/4.31  thf(t17_xboole_1, axiom,
% 4.11/4.31    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 4.11/4.31  thf('17', plain,
% 4.11/4.31      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 4.11/4.31      inference('cnf', [status(esa)], [t17_xboole_1])).
% 4.11/4.31  thf('18', plain,
% 4.11/4.31      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31         (k3_subset_1 @ sk_A @ sk_B)))
% 4.11/4.31         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31               (k3_subset_1 @ sk_A @ sk_B))))),
% 4.11/4.31      inference('split', [status(esa)], ['5'])).
% 4.11/4.31  thf('19', plain,
% 4.11/4.31      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 4.11/4.31      inference('sup-', [status(thm)], ['10', '11'])).
% 4.11/4.31  thf(t106_xboole_1, axiom,
% 4.11/4.31    (![A:$i,B:$i,C:$i]:
% 4.11/4.31     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 4.11/4.31       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 4.11/4.31  thf('20', plain,
% 4.11/4.31      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.11/4.31         ((r1_xboole_0 @ X6 @ X8)
% 4.11/4.31          | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 4.11/4.31      inference('cnf', [status(esa)], [t106_xboole_1])).
% 4.11/4.31  thf('21', plain,
% 4.11/4.31      (![X0 : $i]:
% 4.11/4.31         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 4.11/4.31          | (r1_xboole_0 @ X0 @ sk_B))),
% 4.11/4.31      inference('sup-', [status(thm)], ['19', '20'])).
% 4.11/4.31  thf('22', plain,
% 4.11/4.31      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 4.11/4.31         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31               (k3_subset_1 @ sk_A @ sk_B))))),
% 4.11/4.31      inference('sup-', [status(thm)], ['18', '21'])).
% 4.11/4.31  thf(symmetry_r1_xboole_0, axiom,
% 4.11/4.31    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 4.11/4.31  thf('23', plain,
% 4.11/4.31      (![X2 : $i, X3 : $i]:
% 4.11/4.31         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 4.11/4.31      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.11/4.31  thf('24', plain,
% 4.11/4.31      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 4.11/4.31         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31               (k3_subset_1 @ sk_A @ sk_B))))),
% 4.11/4.31      inference('sup-', [status(thm)], ['22', '23'])).
% 4.11/4.31  thf('25', plain,
% 4.11/4.31      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 4.11/4.31      inference('sup-', [status(thm)], ['2', '3'])).
% 4.11/4.31  thf(commutativity_k3_xboole_0, axiom,
% 4.11/4.31    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 4.11/4.31  thf('26', plain,
% 4.11/4.31      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 4.11/4.31      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 4.11/4.31  thf(t51_xboole_1, axiom,
% 4.11/4.31    (![A:$i,B:$i]:
% 4.11/4.31     ( ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ B ) ) =
% 4.11/4.31       ( A ) ))).
% 4.11/4.31  thf('27', plain,
% 4.11/4.31      (![X17 : $i, X18 : $i]:
% 4.11/4.31         ((k2_xboole_0 @ (k3_xboole_0 @ X17 @ X18) @ (k4_xboole_0 @ X17 @ X18))
% 4.11/4.31           = (X17))),
% 4.11/4.31      inference('cnf', [status(esa)], [t51_xboole_1])).
% 4.11/4.31  thf('28', plain,
% 4.11/4.31      (![X0 : $i, X1 : $i]:
% 4.11/4.31         ((k2_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X1))
% 4.11/4.31           = (X0))),
% 4.11/4.31      inference('sup+', [status(thm)], ['26', '27'])).
% 4.11/4.31  thf(t73_xboole_1, axiom,
% 4.11/4.31    (![A:$i,B:$i,C:$i]:
% 4.11/4.31     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 4.11/4.31       ( r1_tarski @ A @ B ) ))).
% 4.11/4.31  thf('29', plain,
% 4.11/4.31      (![X19 : $i, X20 : $i, X21 : $i]:
% 4.11/4.31         ((r1_tarski @ X19 @ X20)
% 4.11/4.31          | ~ (r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 4.11/4.31          | ~ (r1_xboole_0 @ X19 @ X21))),
% 4.11/4.31      inference('cnf', [status(esa)], [t73_xboole_1])).
% 4.11/4.31  thf('30', plain,
% 4.11/4.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.11/4.31         (~ (r1_tarski @ X2 @ X0)
% 4.11/4.31          | ~ (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 4.11/4.31          | (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)))),
% 4.11/4.31      inference('sup-', [status(thm)], ['28', '29'])).
% 4.11/4.31  thf('31', plain,
% 4.11/4.31      (![X0 : $i]:
% 4.11/4.31         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 4.11/4.31          | (r1_tarski @ X0 @ (k3_xboole_0 @ sk_C_1 @ sk_A))
% 4.11/4.31          | ~ (r1_tarski @ X0 @ sk_A))),
% 4.11/4.31      inference('sup-', [status(thm)], ['25', '30'])).
% 4.11/4.31  thf('32', plain,
% 4.11/4.31      (((~ (r1_tarski @ sk_B @ sk_A)
% 4.11/4.31         | (r1_tarski @ sk_B @ (k3_xboole_0 @ sk_C_1 @ sk_A))))
% 4.11/4.31         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31               (k3_subset_1 @ sk_A @ sk_B))))),
% 4.11/4.31      inference('sup-', [status(thm)], ['24', '31'])).
% 4.11/4.31  thf('33', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.11/4.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.11/4.31  thf(d2_subset_1, axiom,
% 4.11/4.31    (![A:$i,B:$i]:
% 4.11/4.31     ( ( ( v1_xboole_0 @ A ) =>
% 4.11/4.31         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 4.11/4.31       ( ( ~( v1_xboole_0 @ A ) ) =>
% 4.11/4.31         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 4.11/4.31  thf('34', plain,
% 4.11/4.31      (![X31 : $i, X32 : $i]:
% 4.11/4.31         (~ (m1_subset_1 @ X31 @ X32)
% 4.11/4.31          | (r2_hidden @ X31 @ X32)
% 4.11/4.31          | (v1_xboole_0 @ X32))),
% 4.11/4.31      inference('cnf', [status(esa)], [d2_subset_1])).
% 4.11/4.31  thf('35', plain,
% 4.11/4.31      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 4.11/4.31        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 4.11/4.31      inference('sup-', [status(thm)], ['33', '34'])).
% 4.11/4.31  thf(fc1_subset_1, axiom,
% 4.11/4.31    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 4.11/4.31  thf('36', plain, (![X36 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X36))),
% 4.11/4.31      inference('cnf', [status(esa)], [fc1_subset_1])).
% 4.11/4.31  thf('37', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 4.11/4.31      inference('clc', [status(thm)], ['35', '36'])).
% 4.11/4.31  thf(d1_zfmisc_1, axiom,
% 4.11/4.31    (![A:$i,B:$i]:
% 4.11/4.31     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 4.11/4.31       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 4.11/4.31  thf('38', plain,
% 4.11/4.31      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.11/4.31         (~ (r2_hidden @ X27 @ X26)
% 4.11/4.31          | (r1_tarski @ X27 @ X25)
% 4.11/4.31          | ((X26) != (k1_zfmisc_1 @ X25)))),
% 4.11/4.31      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 4.11/4.31  thf('39', plain,
% 4.11/4.31      (![X25 : $i, X27 : $i]:
% 4.11/4.31         ((r1_tarski @ X27 @ X25) | ~ (r2_hidden @ X27 @ (k1_zfmisc_1 @ X25)))),
% 4.11/4.31      inference('simplify', [status(thm)], ['38'])).
% 4.11/4.31  thf('40', plain, ((r1_tarski @ sk_B @ sk_A)),
% 4.11/4.31      inference('sup-', [status(thm)], ['37', '39'])).
% 4.11/4.31  thf('41', plain,
% 4.11/4.31      (((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_C_1 @ sk_A)))
% 4.11/4.31         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31               (k3_subset_1 @ sk_A @ sk_B))))),
% 4.11/4.31      inference('demod', [status(thm)], ['32', '40'])).
% 4.11/4.31  thf(t1_xboole_1, axiom,
% 4.11/4.31    (![A:$i,B:$i,C:$i]:
% 4.11/4.31     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 4.11/4.31       ( r1_tarski @ A @ C ) ))).
% 4.11/4.31  thf('42', plain,
% 4.11/4.31      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.11/4.31         (~ (r1_tarski @ X11 @ X12)
% 4.11/4.31          | ~ (r1_tarski @ X12 @ X13)
% 4.11/4.31          | (r1_tarski @ X11 @ X13))),
% 4.11/4.31      inference('cnf', [status(esa)], [t1_xboole_1])).
% 4.11/4.31  thf('43', plain,
% 4.11/4.31      ((![X0 : $i]:
% 4.11/4.31          ((r1_tarski @ sk_B @ X0)
% 4.11/4.31           | ~ (r1_tarski @ (k3_xboole_0 @ sk_C_1 @ sk_A) @ X0)))
% 4.11/4.31         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31               (k3_subset_1 @ sk_A @ sk_B))))),
% 4.11/4.31      inference('sup-', [status(thm)], ['41', '42'])).
% 4.11/4.31  thf('44', plain,
% 4.11/4.31      (((r1_tarski @ sk_B @ sk_C_1))
% 4.11/4.31         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31               (k3_subset_1 @ sk_A @ sk_B))))),
% 4.11/4.31      inference('sup-', [status(thm)], ['17', '43'])).
% 4.11/4.31  thf('45', plain,
% 4.11/4.31      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 4.11/4.31      inference('split', [status(esa)], ['0'])).
% 4.11/4.31  thf('46', plain,
% 4.11/4.31      (~
% 4.11/4.31       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 4.11/4.31         (k3_subset_1 @ sk_A @ sk_B))) | 
% 4.11/4.31       ((r1_tarski @ sk_B @ sk_C_1))),
% 4.11/4.31      inference('sup-', [status(thm)], ['44', '45'])).
% 4.11/4.31  thf('47', plain, ($false),
% 4.11/4.31      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '46'])).
% 4.11/4.31  
% 4.11/4.31  % SZS output end Refutation
% 4.11/4.31  
% 4.11/4.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
