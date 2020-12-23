%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ReQJlEuo3S

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:12 EST 2020

% Result     : Theorem 6.21s
% Output     : Refutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 109 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  572 (1049 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ( r1_tarski @ ( k4_xboole_0 @ X13 @ X12 ) @ ( k4_xboole_0 @ X13 @ X11 ) ) ) ),
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
    ! [X30: $i,X31: $i] :
      ( ( ( k3_subset_1 @ X30 @ X31 )
        = ( k4_xboole_0 @ X30 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X5 @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X7 ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      | ~ ( r1_xboole_0 @ X17 @ ( k4_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
      = ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
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

thf('33',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ X28 )
      | ( r2_hidden @ X27 @ X28 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X32: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('36',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('37',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X25 @ X24 )
      | ( r1_tarski @ X25 @ X23 )
      | ( X24
       != ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('38',plain,(
    ! [X23: $i,X25: $i] :
      ( ( r1_tarski @ X25 @ X23 )
      | ~ ( r2_hidden @ X25 @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['36','38'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r1_tarski @ ( k4_xboole_0 @ X8 @ X10 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X2: $i,X4: $i] :
      ( ( ( k4_xboole_0 @ X2 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','43'])).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( ( k4_xboole_0 @ X2 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('46',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','15','16','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ReQJlEuo3S
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 6.21/6.40  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.21/6.40  % Solved by: fo/fo7.sh
% 6.21/6.40  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.21/6.40  % done 3312 iterations in 5.942s
% 6.21/6.40  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.21/6.40  % SZS output start Refutation
% 6.21/6.40  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 6.21/6.40  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.21/6.40  thf(sk_A_type, type, sk_A: $i).
% 6.21/6.40  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.21/6.40  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.21/6.40  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.21/6.40  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 6.21/6.40  thf(sk_C_1_type, type, sk_C_1: $i).
% 6.21/6.40  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 6.21/6.40  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 6.21/6.40  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.21/6.40  thf(sk_B_type, type, sk_B: $i).
% 6.21/6.40  thf(t31_subset_1, conjecture,
% 6.21/6.40    (![A:$i,B:$i]:
% 6.21/6.40     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.21/6.40       ( ![C:$i]:
% 6.21/6.40         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.21/6.40           ( ( r1_tarski @ B @ C ) <=>
% 6.21/6.40             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 6.21/6.40  thf(zf_stmt_0, negated_conjecture,
% 6.21/6.40    (~( ![A:$i,B:$i]:
% 6.21/6.40        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.21/6.40          ( ![C:$i]:
% 6.21/6.40            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 6.21/6.40              ( ( r1_tarski @ B @ C ) <=>
% 6.21/6.40                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 6.21/6.40    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 6.21/6.40  thf('0', plain,
% 6.21/6.40      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40           (k3_subset_1 @ sk_A @ sk_B))
% 6.21/6.40        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 6.21/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.21/6.40  thf('1', plain,
% 6.21/6.40      (~
% 6.21/6.40       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40         (k3_subset_1 @ sk_A @ sk_B))) | 
% 6.21/6.40       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 6.21/6.40      inference('split', [status(esa)], ['0'])).
% 6.21/6.40  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 6.21/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.21/6.40  thf(d5_subset_1, axiom,
% 6.21/6.40    (![A:$i,B:$i]:
% 6.21/6.40     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 6.21/6.40       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 6.21/6.40  thf('3', plain,
% 6.21/6.40      (![X30 : $i, X31 : $i]:
% 6.21/6.40         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 6.21/6.40          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 6.21/6.40      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.21/6.40  thf('4', plain,
% 6.21/6.40      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 6.21/6.40      inference('sup-', [status(thm)], ['2', '3'])).
% 6.21/6.40  thf('5', plain,
% 6.21/6.40      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40         (k3_subset_1 @ sk_A @ sk_B))
% 6.21/6.40        | (r1_tarski @ sk_B @ sk_C_1))),
% 6.21/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.21/6.40  thf('6', plain,
% 6.21/6.40      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 6.21/6.40      inference('split', [status(esa)], ['5'])).
% 6.21/6.40  thf(t34_xboole_1, axiom,
% 6.21/6.40    (![A:$i,B:$i,C:$i]:
% 6.21/6.40     ( ( r1_tarski @ A @ B ) =>
% 6.21/6.40       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 6.21/6.40  thf('7', plain,
% 6.21/6.40      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.21/6.40         (~ (r1_tarski @ X11 @ X12)
% 6.21/6.40          | (r1_tarski @ (k4_xboole_0 @ X13 @ X12) @ (k4_xboole_0 @ X13 @ X11)))),
% 6.21/6.40      inference('cnf', [status(esa)], [t34_xboole_1])).
% 6.21/6.40  thf('8', plain,
% 6.21/6.40      ((![X0 : $i]:
% 6.21/6.40          (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B)))
% 6.21/6.40         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 6.21/6.40      inference('sup-', [status(thm)], ['6', '7'])).
% 6.21/6.40  thf('9', plain,
% 6.21/6.40      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40         (k4_xboole_0 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 6.21/6.40      inference('sup+', [status(thm)], ['4', '8'])).
% 6.21/6.40  thf('10', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.21/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.21/6.40  thf('11', plain,
% 6.21/6.40      (![X30 : $i, X31 : $i]:
% 6.21/6.40         (((k3_subset_1 @ X30 @ X31) = (k4_xboole_0 @ X30 @ X31))
% 6.21/6.40          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X30)))),
% 6.21/6.40      inference('cnf', [status(esa)], [d5_subset_1])).
% 6.21/6.40  thf('12', plain,
% 6.21/6.40      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 6.21/6.40      inference('sup-', [status(thm)], ['10', '11'])).
% 6.21/6.40  thf('13', plain,
% 6.21/6.40      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40         (k3_subset_1 @ sk_A @ sk_B))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 6.21/6.40      inference('demod', [status(thm)], ['9', '12'])).
% 6.21/6.40  thf('14', plain,
% 6.21/6.40      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40           (k3_subset_1 @ sk_A @ sk_B)))
% 6.21/6.40         <= (~
% 6.21/6.40             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40               (k3_subset_1 @ sk_A @ sk_B))))),
% 6.21/6.40      inference('split', [status(esa)], ['0'])).
% 6.21/6.40  thf('15', plain,
% 6.21/6.40      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40         (k3_subset_1 @ sk_A @ sk_B))) | 
% 6.21/6.40       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 6.21/6.40      inference('sup-', [status(thm)], ['13', '14'])).
% 6.21/6.40  thf('16', plain,
% 6.21/6.40      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40         (k3_subset_1 @ sk_A @ sk_B))) | 
% 6.21/6.40       ((r1_tarski @ sk_B @ sk_C_1))),
% 6.21/6.40      inference('split', [status(esa)], ['5'])).
% 6.21/6.40  thf('17', plain,
% 6.21/6.40      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40         (k3_subset_1 @ sk_A @ sk_B)))
% 6.21/6.40         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40               (k3_subset_1 @ sk_A @ sk_B))))),
% 6.21/6.40      inference('split', [status(esa)], ['5'])).
% 6.21/6.40  thf('18', plain,
% 6.21/6.40      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 6.21/6.40      inference('sup-', [status(thm)], ['10', '11'])).
% 6.21/6.40  thf(t106_xboole_1, axiom,
% 6.21/6.40    (![A:$i,B:$i,C:$i]:
% 6.21/6.40     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 6.21/6.40       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 6.21/6.40  thf('19', plain,
% 6.21/6.40      (![X5 : $i, X6 : $i, X7 : $i]:
% 6.21/6.40         ((r1_xboole_0 @ X5 @ X7)
% 6.21/6.40          | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X7)))),
% 6.21/6.40      inference('cnf', [status(esa)], [t106_xboole_1])).
% 6.21/6.40  thf('20', plain,
% 6.21/6.40      (![X0 : $i]:
% 6.21/6.40         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 6.21/6.40          | (r1_xboole_0 @ X0 @ sk_B))),
% 6.21/6.40      inference('sup-', [status(thm)], ['18', '19'])).
% 6.21/6.40  thf('21', plain,
% 6.21/6.40      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 6.21/6.40         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40               (k3_subset_1 @ sk_A @ sk_B))))),
% 6.21/6.40      inference('sup-', [status(thm)], ['17', '20'])).
% 6.21/6.40  thf(symmetry_r1_xboole_0, axiom,
% 6.21/6.40    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 6.21/6.40  thf('22', plain,
% 6.21/6.40      (![X0 : $i, X1 : $i]:
% 6.21/6.40         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 6.21/6.40      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 6.21/6.40  thf('23', plain,
% 6.21/6.40      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 6.21/6.40         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40               (k3_subset_1 @ sk_A @ sk_B))))),
% 6.21/6.40      inference('sup-', [status(thm)], ['21', '22'])).
% 6.21/6.40  thf('24', plain,
% 6.21/6.40      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 6.21/6.40      inference('sup-', [status(thm)], ['2', '3'])).
% 6.21/6.40  thf(t81_xboole_1, axiom,
% 6.21/6.40    (![A:$i,B:$i,C:$i]:
% 6.21/6.40     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 6.21/6.40       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 6.21/6.40  thf('25', plain,
% 6.21/6.40      (![X16 : $i, X17 : $i, X18 : $i]:
% 6.21/6.40         ((r1_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 6.21/6.40          | ~ (r1_xboole_0 @ X17 @ (k4_xboole_0 @ X16 @ X18)))),
% 6.21/6.40      inference('cnf', [status(esa)], [t81_xboole_1])).
% 6.21/6.40  thf('26', plain,
% 6.21/6.40      (![X0 : $i]:
% 6.21/6.40         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 6.21/6.40          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 6.21/6.40      inference('sup-', [status(thm)], ['24', '25'])).
% 6.21/6.40  thf('27', plain,
% 6.21/6.40      (((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)))
% 6.21/6.40         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40               (k3_subset_1 @ sk_A @ sk_B))))),
% 6.21/6.40      inference('sup-', [status(thm)], ['23', '26'])).
% 6.21/6.40  thf('28', plain,
% 6.21/6.40      (![X0 : $i, X1 : $i]:
% 6.21/6.40         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 6.21/6.40      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 6.21/6.40  thf('29', plain,
% 6.21/6.40      (((r1_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A))
% 6.21/6.40         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40               (k3_subset_1 @ sk_A @ sk_B))))),
% 6.21/6.40      inference('sup-', [status(thm)], ['27', '28'])).
% 6.21/6.40  thf(t83_xboole_1, axiom,
% 6.21/6.40    (![A:$i,B:$i]:
% 6.21/6.40     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 6.21/6.40  thf('30', plain,
% 6.21/6.40      (![X19 : $i, X20 : $i]:
% 6.21/6.40         (((k4_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_xboole_0 @ X19 @ X20))),
% 6.21/6.40      inference('cnf', [status(esa)], [t83_xboole_1])).
% 6.21/6.40  thf('31', plain,
% 6.21/6.40      ((((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 6.21/6.40          = (k4_xboole_0 @ sk_B @ sk_C_1)))
% 6.21/6.40         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40               (k3_subset_1 @ sk_A @ sk_B))))),
% 6.21/6.40      inference('sup-', [status(thm)], ['29', '30'])).
% 6.21/6.40  thf('32', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.21/6.40      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.21/6.40  thf(d2_subset_1, axiom,
% 6.21/6.40    (![A:$i,B:$i]:
% 6.21/6.40     ( ( ( v1_xboole_0 @ A ) =>
% 6.21/6.40         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 6.21/6.40       ( ( ~( v1_xboole_0 @ A ) ) =>
% 6.21/6.40         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 6.21/6.40  thf('33', plain,
% 6.21/6.40      (![X27 : $i, X28 : $i]:
% 6.21/6.40         (~ (m1_subset_1 @ X27 @ X28)
% 6.21/6.40          | (r2_hidden @ X27 @ X28)
% 6.21/6.40          | (v1_xboole_0 @ X28))),
% 6.21/6.40      inference('cnf', [status(esa)], [d2_subset_1])).
% 6.21/6.40  thf('34', plain,
% 6.21/6.40      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 6.21/6.40        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 6.21/6.40      inference('sup-', [status(thm)], ['32', '33'])).
% 6.21/6.40  thf(fc1_subset_1, axiom,
% 6.21/6.40    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 6.21/6.40  thf('35', plain, (![X32 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 6.21/6.40      inference('cnf', [status(esa)], [fc1_subset_1])).
% 6.21/6.40  thf('36', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 6.21/6.40      inference('clc', [status(thm)], ['34', '35'])).
% 6.21/6.40  thf(d1_zfmisc_1, axiom,
% 6.21/6.40    (![A:$i,B:$i]:
% 6.21/6.40     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 6.21/6.40       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 6.21/6.40  thf('37', plain,
% 6.21/6.40      (![X23 : $i, X24 : $i, X25 : $i]:
% 6.21/6.40         (~ (r2_hidden @ X25 @ X24)
% 6.21/6.40          | (r1_tarski @ X25 @ X23)
% 6.21/6.40          | ((X24) != (k1_zfmisc_1 @ X23)))),
% 6.21/6.40      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 6.21/6.40  thf('38', plain,
% 6.21/6.40      (![X23 : $i, X25 : $i]:
% 6.21/6.40         ((r1_tarski @ X25 @ X23) | ~ (r2_hidden @ X25 @ (k1_zfmisc_1 @ X23)))),
% 6.21/6.40      inference('simplify', [status(thm)], ['37'])).
% 6.21/6.40  thf('39', plain, ((r1_tarski @ sk_B @ sk_A)),
% 6.21/6.40      inference('sup-', [status(thm)], ['36', '38'])).
% 6.21/6.40  thf(t109_xboole_1, axiom,
% 6.21/6.40    (![A:$i,B:$i,C:$i]:
% 6.21/6.40     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 6.21/6.40  thf('40', plain,
% 6.21/6.40      (![X8 : $i, X9 : $i, X10 : $i]:
% 6.21/6.40         (~ (r1_tarski @ X8 @ X9) | (r1_tarski @ (k4_xboole_0 @ X8 @ X10) @ X9))),
% 6.21/6.40      inference('cnf', [status(esa)], [t109_xboole_1])).
% 6.21/6.40  thf('41', plain,
% 6.21/6.40      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 6.21/6.40      inference('sup-', [status(thm)], ['39', '40'])).
% 6.21/6.40  thf(l32_xboole_1, axiom,
% 6.21/6.40    (![A:$i,B:$i]:
% 6.21/6.40     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.21/6.40  thf('42', plain,
% 6.21/6.40      (![X2 : $i, X4 : $i]:
% 6.21/6.40         (((k4_xboole_0 @ X2 @ X4) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ X4))),
% 6.21/6.40      inference('cnf', [status(esa)], [l32_xboole_1])).
% 6.21/6.40  thf('43', plain,
% 6.21/6.40      (![X0 : $i]:
% 6.21/6.40         ((k4_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ sk_A) = (k1_xboole_0))),
% 6.21/6.40      inference('sup-', [status(thm)], ['41', '42'])).
% 6.21/6.40  thf('44', plain,
% 6.21/6.40      ((((k1_xboole_0) = (k4_xboole_0 @ sk_B @ sk_C_1)))
% 6.21/6.40         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40               (k3_subset_1 @ sk_A @ sk_B))))),
% 6.21/6.40      inference('demod', [status(thm)], ['31', '43'])).
% 6.21/6.40  thf('45', plain,
% 6.21/6.40      (![X2 : $i, X3 : $i]:
% 6.21/6.40         ((r1_tarski @ X2 @ X3) | ((k4_xboole_0 @ X2 @ X3) != (k1_xboole_0)))),
% 6.21/6.40      inference('cnf', [status(esa)], [l32_xboole_1])).
% 6.21/6.40  thf('46', plain,
% 6.21/6.40      (((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_C_1)))
% 6.21/6.40         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40               (k3_subset_1 @ sk_A @ sk_B))))),
% 6.21/6.40      inference('sup-', [status(thm)], ['44', '45'])).
% 6.21/6.40  thf('47', plain,
% 6.21/6.40      (((r1_tarski @ sk_B @ sk_C_1))
% 6.21/6.40         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40               (k3_subset_1 @ sk_A @ sk_B))))),
% 6.21/6.40      inference('simplify', [status(thm)], ['46'])).
% 6.21/6.40  thf('48', plain,
% 6.21/6.40      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 6.21/6.40      inference('split', [status(esa)], ['0'])).
% 6.21/6.40  thf('49', plain,
% 6.21/6.40      (~
% 6.21/6.40       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 6.21/6.40         (k3_subset_1 @ sk_A @ sk_B))) | 
% 6.21/6.40       ((r1_tarski @ sk_B @ sk_C_1))),
% 6.21/6.40      inference('sup-', [status(thm)], ['47', '48'])).
% 6.21/6.40  thf('50', plain, ($false),
% 6.21/6.40      inference('sat_resolution*', [status(thm)], ['1', '15', '16', '49'])).
% 6.21/6.40  
% 6.21/6.40  % SZS output end Refutation
% 6.21/6.40  
% 6.21/6.41  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
