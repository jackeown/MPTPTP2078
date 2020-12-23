%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XMK4yWvc3v

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:10 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 113 expanded)
%              Number of leaves         :   23 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :  550 (1087 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

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
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
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
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
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

thf('17',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['5'])).

thf('18',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('25',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X19 ) )
      = ( k2_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_tarski @ X21 @ ( k2_xboole_0 @ X22 @ X23 ) )
      | ~ ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('30',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('32',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('33',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('34',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( r1_tarski @ X27 @ X25 )
      | ( X26
       != ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('35',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['33','35'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('38',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_tarski @ X0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','38'])).

thf('40',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( r1_tarski @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('45',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('47',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','47'])).

thf('49',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XMK4yWvc3v
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.75/0.95  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.95  % Solved by: fo/fo7.sh
% 0.75/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.95  % done 817 iterations in 0.478s
% 0.75/0.95  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.95  % SZS output start Refutation
% 0.75/0.95  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.95  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.75/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.95  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.75/0.95  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.75/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.95  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.75/0.95  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.95  thf(t31_subset_1, conjecture,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.95       ( ![C:$i]:
% 0.75/0.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.95           ( ( r1_tarski @ B @ C ) <=>
% 0.75/0.95             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.75/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.95    (~( ![A:$i,B:$i]:
% 0.75/0.95        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.95          ( ![C:$i]:
% 0.75/0.95            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.95              ( ( r1_tarski @ B @ C ) <=>
% 0.75/0.95                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.75/0.95    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.75/0.95  thf('0', plain,
% 0.75/0.95      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95           (k3_subset_1 @ sk_A @ sk_B))
% 0.75/0.95        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('1', plain,
% 0.75/0.95      (~
% 0.75/0.95       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.75/0.95       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.95      inference('split', [status(esa)], ['0'])).
% 0.75/0.95  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(d5_subset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.95       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.75/0.95  thf('3', plain,
% 0.75/0.95      (![X32 : $i, X33 : $i]:
% 0.75/0.95         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 0.75/0.95          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.75/0.95  thf('4', plain,
% 0.75/0.95      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.95  thf('5', plain,
% 0.75/0.95      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95         (k3_subset_1 @ sk_A @ sk_B))
% 0.75/0.95        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('6', plain,
% 0.75/0.95      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.75/0.95      inference('split', [status(esa)], ['5'])).
% 0.75/0.95  thf(t34_xboole_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( r1_tarski @ A @ B ) =>
% 0.75/0.95       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.75/0.95  thf('7', plain,
% 0.75/0.95      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.75/0.95         (~ (r1_tarski @ X14 @ X15)
% 0.75/0.95          | (r1_tarski @ (k4_xboole_0 @ X16 @ X15) @ (k4_xboole_0 @ X16 @ X14)))),
% 0.75/0.95      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.75/0.95  thf('8', plain,
% 0.75/0.95      ((![X0 : $i]:
% 0.75/0.95          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.75/0.95         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['6', '7'])).
% 0.75/0.95  thf('9', plain,
% 0.75/0.95      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.75/0.95      inference('sup+', [status(thm)], ['4', '8'])).
% 0.75/0.95  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('11', plain,
% 0.75/0.95      (![X32 : $i, X33 : $i]:
% 0.75/0.95         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 0.75/0.95          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.75/0.95      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.75/0.95  thf('12', plain,
% 0.75/0.95      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.95  thf('13', plain,
% 0.75/0.95      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.75/0.95      inference('demod', [status(thm)], ['9', '12'])).
% 0.75/0.95  thf('14', plain,
% 0.75/0.95      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95           (k3_subset_1 @ sk_A @ sk_B)))
% 0.75/0.95         <= (~
% 0.75/0.95             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.75/0.95      inference('split', [status(esa)], ['0'])).
% 0.75/0.95  thf('15', plain,
% 0.75/0.95      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.75/0.95       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['13', '14'])).
% 0.75/0.95  thf('16', plain,
% 0.75/0.95      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.75/0.95       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.95      inference('split', [status(esa)], ['5'])).
% 0.75/0.95  thf('17', plain,
% 0.75/0.95      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95         (k3_subset_1 @ sk_A @ sk_B)))
% 0.75/0.95         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.75/0.95      inference('split', [status(esa)], ['5'])).
% 0.75/0.95  thf('18', plain,
% 0.75/0.95      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['10', '11'])).
% 0.75/0.95  thf(t106_xboole_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.75/0.95       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.75/0.95  thf('19', plain,
% 0.75/0.95      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.75/0.95         ((r1_xboole_0 @ X6 @ X8)
% 0.75/0.95          | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.75/0.95      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.75/0.95  thf('20', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.75/0.95          | (r1_xboole_0 @ X0 @ sk_B))),
% 0.75/0.95      inference('sup-', [status(thm)], ['18', '19'])).
% 0.75/0.95  thf('21', plain,
% 0.75/0.95      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.75/0.95         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['17', '20'])).
% 0.75/0.95  thf(symmetry_r1_xboole_0, axiom,
% 0.75/0.95    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.75/0.95  thf('22', plain,
% 0.75/0.95      (![X2 : $i, X3 : $i]:
% 0.75/0.95         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.75/0.95      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.75/0.95  thf('23', plain,
% 0.75/0.95      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.75/0.95         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/0.95  thf('24', plain,
% 0.75/0.95      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.75/0.95  thf(t39_xboole_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.75/0.95  thf('25', plain,
% 0.75/0.95      (![X19 : $i, X20 : $i]:
% 0.75/0.95         ((k2_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X19))
% 0.75/0.95           = (k2_xboole_0 @ X19 @ X20))),
% 0.75/0.95      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.75/0.95  thf(t73_xboole_1, axiom,
% 0.75/0.95    (![A:$i,B:$i,C:$i]:
% 0.75/0.95     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.75/0.95       ( r1_tarski @ A @ B ) ))).
% 0.75/0.95  thf('26', plain,
% 0.75/0.95      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.75/0.95         ((r1_tarski @ X21 @ X22)
% 0.75/0.95          | ~ (r1_tarski @ X21 @ (k2_xboole_0 @ X22 @ X23))
% 0.75/0.95          | ~ (r1_xboole_0 @ X21 @ X23))),
% 0.75/0.95      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.75/0.95  thf('27', plain,
% 0.75/0.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.95         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.75/0.95          | ~ (r1_xboole_0 @ X2 @ (k4_xboole_0 @ X0 @ X1))
% 0.75/0.95          | (r1_tarski @ X2 @ X1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/0.95  thf('28', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.75/0.95          | (r1_tarski @ X0 @ sk_C_1)
% 0.75/0.95          | ~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['24', '27'])).
% 0.75/0.95  thf('29', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf(d2_subset_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ( v1_xboole_0 @ A ) =>
% 0.75/0.95         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.75/0.95       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.75/0.95         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.75/0.95  thf('30', plain,
% 0.75/0.95      (![X29 : $i, X30 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X29 @ X30)
% 0.75/0.95          | (r2_hidden @ X29 @ X30)
% 0.75/0.95          | (v1_xboole_0 @ X30))),
% 0.75/0.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.75/0.95  thf('31', plain,
% 0.75/0.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.95        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/0.95  thf(fc1_subset_1, axiom,
% 0.75/0.95    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.75/0.95  thf('32', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 0.75/0.95      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.75/0.95  thf('33', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['31', '32'])).
% 0.75/0.95  thf(d1_zfmisc_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.75/0.95       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.75/0.95  thf('34', plain,
% 0.75/0.95      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.75/0.95         (~ (r2_hidden @ X27 @ X26)
% 0.75/0.95          | (r1_tarski @ X27 @ X25)
% 0.75/0.95          | ((X26) != (k1_zfmisc_1 @ X25)))),
% 0.75/0.95      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.75/0.95  thf('35', plain,
% 0.75/0.95      (![X25 : $i, X27 : $i]:
% 0.75/0.95         ((r1_tarski @ X27 @ X25) | ~ (r2_hidden @ X27 @ (k1_zfmisc_1 @ X25)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['34'])).
% 0.75/0.95  thf('36', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 0.75/0.95      inference('sup-', [status(thm)], ['33', '35'])).
% 0.75/0.95  thf(t12_xboole_1, axiom,
% 0.75/0.95    (![A:$i,B:$i]:
% 0.75/0.95     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.75/0.95  thf('37', plain,
% 0.75/0.95      (![X12 : $i, X13 : $i]:
% 0.75/0.95         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 0.75/0.95      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.75/0.95  thf('38', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 0.75/0.95      inference('sup-', [status(thm)], ['36', '37'])).
% 0.75/0.95  thf('39', plain,
% 0.75/0.95      (![X0 : $i]:
% 0.75/0.95         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.75/0.95          | (r1_tarski @ X0 @ sk_C_1)
% 0.75/0.95          | ~ (r1_tarski @ X0 @ sk_A))),
% 0.75/0.95      inference('demod', [status(thm)], ['28', '38'])).
% 0.75/0.95  thf('40', plain,
% 0.75/0.95      (((~ (r1_tarski @ sk_B @ sk_A) | (r1_tarski @ sk_B @ sk_C_1)))
% 0.75/0.95         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.75/0.95      inference('sup-', [status(thm)], ['23', '39'])).
% 0.75/0.95  thf('41', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.95  thf('42', plain,
% 0.75/0.95      (![X29 : $i, X30 : $i]:
% 0.75/0.95         (~ (m1_subset_1 @ X29 @ X30)
% 0.75/0.95          | (r2_hidden @ X29 @ X30)
% 0.75/0.95          | (v1_xboole_0 @ X30))),
% 0.75/0.95      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.75/0.95  thf('43', plain,
% 0.75/0.95      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.95        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.75/0.95      inference('sup-', [status(thm)], ['41', '42'])).
% 0.75/0.95  thf('44', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 0.75/0.95      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.75/0.95  thf('45', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.95      inference('clc', [status(thm)], ['43', '44'])).
% 0.75/0.95  thf('46', plain,
% 0.75/0.95      (![X25 : $i, X27 : $i]:
% 0.75/0.95         ((r1_tarski @ X27 @ X25) | ~ (r2_hidden @ X27 @ (k1_zfmisc_1 @ X25)))),
% 0.75/0.95      inference('simplify', [status(thm)], ['34'])).
% 0.75/0.95  thf('47', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.75/0.95      inference('sup-', [status(thm)], ['45', '46'])).
% 0.75/0.95  thf('48', plain,
% 0.75/0.95      (((r1_tarski @ sk_B @ sk_C_1))
% 0.75/0.95         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.75/0.95      inference('demod', [status(thm)], ['40', '47'])).
% 0.75/0.95  thf('49', plain,
% 0.75/0.95      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.75/0.95      inference('split', [status(esa)], ['0'])).
% 0.75/0.95  thf('50', plain,
% 0.75/0.95      (~
% 0.75/0.95       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.75/0.95         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.75/0.95       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.75/0.95      inference('sup-', [status(thm)], ['48', '49'])).
% 0.75/0.95  thf('51', plain, ($false),
% 0.75/0.95      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '50'])).
% 0.75/0.95  
% 0.75/0.95  % SZS output end Refutation
% 0.75/0.95  
% 0.75/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
