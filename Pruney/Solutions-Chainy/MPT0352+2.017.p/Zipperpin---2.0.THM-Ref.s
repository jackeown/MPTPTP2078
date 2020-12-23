%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8DspZZfeCx

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:09 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 103 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  516 ( 979 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

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
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_tarski @ ( k4_xboole_0 @ X19 @ X18 ) @ ( k4_xboole_0 @ X19 @ X17 ) ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k3_subset_1 @ X36 @ X37 )
        = ( k4_xboole_0 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X9 @ X11 )
      | ~ ( r1_tarski @ X9 @ ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r1_tarski @ X22 @ ( k2_xboole_0 @ X23 @ X24 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X22 @ X23 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X38: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('34',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['32','33'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('35',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( r1_tarski @ X31 @ X29 )
      | ( X30
       != ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('36',plain,(
    ! [X29: $i,X31: $i] :
      ( ( r1_tarski @ X31 @ X29 )
      | ~ ( r2_hidden @ X31 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['34','36'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_tarski @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
      | ~ ( r1_xboole_0 @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('42',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('45',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8DspZZfeCx
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:54:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.81  % Solved by: fo/fo7.sh
% 0.60/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.81  % done 1108 iterations in 0.356s
% 0.60/0.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.81  % SZS output start Refutation
% 0.60/0.81  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.81  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.60/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.81  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.60/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.81  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.81  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.81  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.60/0.81  thf(t31_subset_1, conjecture,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.81       ( ![C:$i]:
% 0.60/0.81         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.81           ( ( r1_tarski @ B @ C ) <=>
% 0.60/0.81             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.60/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.81    (~( ![A:$i,B:$i]:
% 0.60/0.81        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.81          ( ![C:$i]:
% 0.60/0.81            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.81              ( ( r1_tarski @ B @ C ) <=>
% 0.60/0.81                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.60/0.81    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.60/0.81  thf('0', plain,
% 0.60/0.81      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81           (k3_subset_1 @ sk_A @ sk_B))
% 0.60/0.81        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('1', plain,
% 0.60/0.81      (~
% 0.60/0.81       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.60/0.81       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.60/0.81      inference('split', [status(esa)], ['0'])).
% 0.60/0.81  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(d5_subset_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.60/0.81       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.60/0.81  thf('3', plain,
% 0.60/0.81      (![X36 : $i, X37 : $i]:
% 0.60/0.81         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.60/0.81          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.60/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.60/0.81  thf('4', plain,
% 0.60/0.81      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.60/0.81      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.81  thf('5', plain,
% 0.60/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81         (k3_subset_1 @ sk_A @ sk_B))
% 0.60/0.81        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('6', plain,
% 0.60/0.81      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.60/0.81      inference('split', [status(esa)], ['5'])).
% 0.60/0.81  thf(t34_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( r1_tarski @ A @ B ) =>
% 0.60/0.81       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.60/0.81  thf('7', plain,
% 0.60/0.81      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X17 @ X18)
% 0.60/0.81          | (r1_tarski @ (k4_xboole_0 @ X19 @ X18) @ (k4_xboole_0 @ X19 @ X17)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.60/0.81  thf('8', plain,
% 0.60/0.81      ((![X0 : $i]:
% 0.60/0.81          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 0.60/0.81         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.81  thf('9', plain,
% 0.60/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.60/0.81      inference('sup+', [status(thm)], ['4', '8'])).
% 0.60/0.81  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('11', plain,
% 0.60/0.81      (![X36 : $i, X37 : $i]:
% 0.60/0.81         (((k3_subset_1 @ X36 @ X37) = (k4_xboole_0 @ X36 @ X37))
% 0.60/0.81          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36)))),
% 0.60/0.81      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.60/0.81  thf('12', plain,
% 0.60/0.81      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.81  thf('13', plain,
% 0.60/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.60/0.81      inference('demod', [status(thm)], ['9', '12'])).
% 0.60/0.81  thf('14', plain,
% 0.60/0.81      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81           (k3_subset_1 @ sk_A @ sk_B)))
% 0.60/0.81         <= (~
% 0.60/0.81             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.60/0.81      inference('split', [status(esa)], ['0'])).
% 0.60/0.81  thf('15', plain,
% 0.60/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.60/0.81       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.60/0.81      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.81  thf('16', plain,
% 0.60/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.60/0.81       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.60/0.81      inference('split', [status(esa)], ['5'])).
% 0.60/0.81  thf('17', plain,
% 0.60/0.81      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81         (k3_subset_1 @ sk_A @ sk_B)))
% 0.60/0.81         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.60/0.81      inference('split', [status(esa)], ['5'])).
% 0.60/0.81  thf('18', plain,
% 0.60/0.81      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.81  thf(t106_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.60/0.81       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.60/0.81  thf('19', plain,
% 0.60/0.81      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.81         ((r1_xboole_0 @ X9 @ X11)
% 0.60/0.81          | ~ (r1_tarski @ X9 @ (k4_xboole_0 @ X10 @ X11)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.60/0.81  thf('20', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.60/0.81          | (r1_xboole_0 @ X0 @ sk_B))),
% 0.60/0.81      inference('sup-', [status(thm)], ['18', '19'])).
% 0.60/0.81  thf('21', plain,
% 0.60/0.81      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.60/0.81         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.60/0.81      inference('sup-', [status(thm)], ['17', '20'])).
% 0.60/0.81  thf(symmetry_r1_xboole_0, axiom,
% 0.60/0.81    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.60/0.81  thf('22', plain,
% 0.60/0.81      (![X2 : $i, X3 : $i]:
% 0.60/0.81         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.60/0.81      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.60/0.81  thf('23', plain,
% 0.60/0.81      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.60/0.81         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.60/0.81      inference('sup-', [status(thm)], ['21', '22'])).
% 0.60/0.81  thf('24', plain,
% 0.60/0.81      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.60/0.81      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.81  thf(d10_xboole_0, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.81  thf('25', plain,
% 0.60/0.81      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.60/0.81      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.60/0.81  thf('26', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.60/0.81      inference('simplify', [status(thm)], ['25'])).
% 0.60/0.81  thf(t44_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.60/0.81       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.60/0.81  thf('27', plain,
% 0.60/0.81      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.60/0.81         ((r1_tarski @ X22 @ (k2_xboole_0 @ X23 @ X24))
% 0.60/0.81          | ~ (r1_tarski @ (k4_xboole_0 @ X22 @ X23) @ X24))),
% 0.60/0.81      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.60/0.81  thf('28', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['26', '27'])).
% 0.60/0.81  thf('29', plain,
% 0.60/0.81      ((r1_tarski @ sk_A @ 
% 0.60/0.81        (k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.60/0.81      inference('sup+', [status(thm)], ['24', '28'])).
% 0.60/0.81  thf('30', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(d2_subset_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( ( v1_xboole_0 @ A ) =>
% 0.60/0.81         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.60/0.81       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.60/0.81         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.60/0.81  thf('31', plain,
% 0.60/0.81      (![X33 : $i, X34 : $i]:
% 0.60/0.81         (~ (m1_subset_1 @ X33 @ X34)
% 0.60/0.81          | (r2_hidden @ X33 @ X34)
% 0.60/0.81          | (v1_xboole_0 @ X34))),
% 0.60/0.81      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.60/0.81  thf('32', plain,
% 0.60/0.81      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.60/0.81        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['30', '31'])).
% 0.60/0.81  thf(fc1_subset_1, axiom,
% 0.60/0.81    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.60/0.81  thf('33', plain, (![X38 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 0.60/0.81      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.60/0.81  thf('34', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.60/0.81      inference('clc', [status(thm)], ['32', '33'])).
% 0.60/0.81  thf(d1_zfmisc_1, axiom,
% 0.60/0.81    (![A:$i,B:$i]:
% 0.60/0.81     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.60/0.81       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.60/0.81  thf('35', plain,
% 0.60/0.81      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.60/0.81         (~ (r2_hidden @ X31 @ X30)
% 0.60/0.81          | (r1_tarski @ X31 @ X29)
% 0.60/0.81          | ((X30) != (k1_zfmisc_1 @ X29)))),
% 0.60/0.81      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.60/0.81  thf('36', plain,
% 0.60/0.81      (![X29 : $i, X31 : $i]:
% 0.60/0.81         ((r1_tarski @ X31 @ X29) | ~ (r2_hidden @ X31 @ (k1_zfmisc_1 @ X29)))),
% 0.60/0.81      inference('simplify', [status(thm)], ['35'])).
% 0.60/0.81  thf('37', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.60/0.81      inference('sup-', [status(thm)], ['34', '36'])).
% 0.60/0.81  thf(t1_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.60/0.81       ( r1_tarski @ A @ C ) ))).
% 0.60/0.81  thf('38', plain,
% 0.60/0.81      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X14 @ X15)
% 0.60/0.81          | ~ (r1_tarski @ X15 @ X16)
% 0.60/0.81          | (r1_tarski @ X14 @ X16))),
% 0.60/0.81      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.60/0.81  thf('39', plain,
% 0.60/0.81      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['37', '38'])).
% 0.60/0.81  thf('40', plain,
% 0.60/0.81      ((r1_tarski @ sk_B @ 
% 0.60/0.81        (k2_xboole_0 @ sk_C_1 @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['29', '39'])).
% 0.60/0.81  thf(t73_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.60/0.81       ( r1_tarski @ A @ B ) ))).
% 0.60/0.81  thf('41', plain,
% 0.60/0.81      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.60/0.81         ((r1_tarski @ X25 @ X26)
% 0.60/0.81          | ~ (r1_tarski @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 0.60/0.81          | ~ (r1_xboole_0 @ X25 @ X27))),
% 0.60/0.81      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.60/0.81  thf('42', plain,
% 0.60/0.81      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.60/0.81        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.60/0.81      inference('sup-', [status(thm)], ['40', '41'])).
% 0.60/0.81  thf('43', plain,
% 0.60/0.81      (((r1_tarski @ sk_B @ sk_C_1))
% 0.60/0.81         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.60/0.81      inference('sup-', [status(thm)], ['23', '42'])).
% 0.60/0.81  thf('44', plain,
% 0.60/0.81      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.60/0.81      inference('split', [status(esa)], ['0'])).
% 0.60/0.81  thf('45', plain,
% 0.60/0.81      (~
% 0.60/0.81       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.60/0.81         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.60/0.81       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.60/0.81      inference('sup-', [status(thm)], ['43', '44'])).
% 0.60/0.81  thf('46', plain, ($false),
% 0.60/0.81      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '45'])).
% 0.60/0.81  
% 0.60/0.81  % SZS output end Refutation
% 0.60/0.81  
% 0.60/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
