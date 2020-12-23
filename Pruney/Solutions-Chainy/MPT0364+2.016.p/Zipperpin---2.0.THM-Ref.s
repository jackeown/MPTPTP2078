%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Sp1PZqidqd

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:04 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 147 expanded)
%              Number of leaves         :   24 (  49 expanded)
%              Depth                    :   17
%              Number of atoms          :  528 (1244 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t44_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
          <=> ( r1_tarski @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) )
            <=> ( r1_tarski @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t44_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_xboole_0 @ X16 @ ( k4_xboole_0 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('9',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['5','9'])).

thf('11',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','12'])).

thf('14',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['6'])).

thf('16',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['6'])).

thf('17',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','12','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['15','17'])).

thf('19',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t81_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) )
      | ~ ( r1_xboole_0 @ X11 @ ( k4_xboole_0 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ( r2_hidden @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('26',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('27',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X22 @ X21 )
      | ( r1_tarski @ X22 @ X20 )
      | ( X21
       != ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('29',plain,(
    ! [X20: $i,X22: $i] :
      ( ( r1_tarski @ X22 @ X20 )
      | ~ ( r2_hidden @ X22 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['27','29'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('31',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X9 )
      | ( r1_xboole_0 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k4_xboole_0 @ X13 @ X14 )
        = X13 )
      | ~ ( r1_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = sk_B ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('36',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r2_hidden @ X19 @ X21 )
      | ( X21
       != ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('38',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ( m1_subset_1 @ X24 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X29: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k3_subset_1 @ X27 @ X28 )
        = ( k4_xboole_0 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k3_subset_1 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = sk_B ),
    inference(demod,[status(thm)],['35','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('48',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ ( k4_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_subset_1 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_B )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X3 @ X4 ) @ X3 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('52',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['50','51'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['14','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Sp1PZqidqd
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:42:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.67/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.90  % Solved by: fo/fo7.sh
% 0.67/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.90  % done 839 iterations in 0.445s
% 0.67/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.90  % SZS output start Refutation
% 0.67/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.67/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.90  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.67/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.67/0.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.67/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.90  thf(t44_subset_1, conjecture,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.90       ( ![C:$i]:
% 0.67/0.90         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.90           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.67/0.90             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.67/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.90    (~( ![A:$i,B:$i]:
% 0.67/0.90        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.90          ( ![C:$i]:
% 0.67/0.90            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.90              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.67/0.90                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.67/0.90    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.67/0.90  thf('0', plain,
% 0.67/0.90      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.67/0.90        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('1', plain,
% 0.67/0.90      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.67/0.90      inference('split', [status(esa)], ['0'])).
% 0.67/0.90  thf('2', plain,
% 0.67/0.90      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.67/0.90       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.67/0.90      inference('split', [status(esa)], ['0'])).
% 0.67/0.90  thf('3', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf(d5_subset_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.90       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.67/0.90  thf('4', plain,
% 0.67/0.90      (![X27 : $i, X28 : $i]:
% 0.67/0.90         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.67/0.90          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.67/0.90      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.67/0.90  thf('5', plain,
% 0.67/0.90      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.67/0.90      inference('sup-', [status(thm)], ['3', '4'])).
% 0.67/0.90  thf('6', plain,
% 0.67/0.90      (((r1_tarski @ sk_B @ sk_C_1)
% 0.67/0.90        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf('7', plain,
% 0.67/0.90      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.67/0.90      inference('split', [status(esa)], ['6'])).
% 0.67/0.90  thf(t85_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i,C:$i]:
% 0.67/0.90     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.67/0.90  thf('8', plain,
% 0.67/0.90      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.67/0.90         (~ (r1_tarski @ X16 @ X17)
% 0.67/0.90          | (r1_xboole_0 @ X16 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.67/0.90  thf('9', plain,
% 0.67/0.90      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 0.67/0.90         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['7', '8'])).
% 0.67/0.90  thf('10', plain,
% 0.67/0.90      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.67/0.90         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.67/0.90      inference('sup+', [status(thm)], ['5', '9'])).
% 0.67/0.90  thf('11', plain,
% 0.67/0.90      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.67/0.90         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.67/0.90      inference('split', [status(esa)], ['0'])).
% 0.67/0.90  thf('12', plain,
% 0.67/0.90      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.67/0.90       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.67/0.90      inference('sup-', [status(thm)], ['10', '11'])).
% 0.67/0.90  thf('13', plain, (~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.67/0.90      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.67/0.90  thf('14', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.67/0.90      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.67/0.90  thf('15', plain,
% 0.67/0.90      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.67/0.90         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.67/0.90      inference('split', [status(esa)], ['6'])).
% 0.67/0.90  thf('16', plain,
% 0.67/0.90      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.67/0.90       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.67/0.90      inference('split', [status(esa)], ['6'])).
% 0.67/0.90  thf('17', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.67/0.90      inference('sat_resolution*', [status(thm)], ['2', '12', '16'])).
% 0.67/0.90  thf('18', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.67/0.90      inference('simpl_trail', [status(thm)], ['15', '17'])).
% 0.67/0.90  thf('19', plain,
% 0.67/0.90      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.67/0.90      inference('sup-', [status(thm)], ['3', '4'])).
% 0.67/0.90  thf(t81_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i,C:$i]:
% 0.67/0.90     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.67/0.90       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.67/0.90  thf('20', plain,
% 0.67/0.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.67/0.90         ((r1_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X12))
% 0.67/0.90          | ~ (r1_xboole_0 @ X11 @ (k4_xboole_0 @ X10 @ X12)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.67/0.90  thf('21', plain,
% 0.67/0.90      (![X0 : $i]:
% 0.67/0.90         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.67/0.90          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['19', '20'])).
% 0.67/0.90  thf('22', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.67/0.90      inference('sup-', [status(thm)], ['18', '21'])).
% 0.67/0.90  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.90  thf(d2_subset_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ( v1_xboole_0 @ A ) =>
% 0.67/0.90         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.67/0.90       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.67/0.90         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.67/0.90  thf('24', plain,
% 0.67/0.90      (![X24 : $i, X25 : $i]:
% 0.67/0.90         (~ (m1_subset_1 @ X24 @ X25)
% 0.67/0.90          | (r2_hidden @ X24 @ X25)
% 0.67/0.90          | (v1_xboole_0 @ X25))),
% 0.67/0.90      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.67/0.90  thf('25', plain,
% 0.67/0.90      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.67/0.90        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['23', '24'])).
% 0.67/0.90  thf(fc1_subset_1, axiom,
% 0.67/0.90    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.67/0.90  thf('26', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.67/0.90      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.67/0.90  thf('27', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.67/0.90      inference('clc', [status(thm)], ['25', '26'])).
% 0.67/0.90  thf(d1_zfmisc_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.67/0.90       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.67/0.90  thf('28', plain,
% 0.67/0.90      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.67/0.90         (~ (r2_hidden @ X22 @ X21)
% 0.67/0.90          | (r1_tarski @ X22 @ X20)
% 0.67/0.90          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 0.67/0.90      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.67/0.90  thf('29', plain,
% 0.67/0.90      (![X20 : $i, X22 : $i]:
% 0.67/0.90         ((r1_tarski @ X22 @ X20) | ~ (r2_hidden @ X22 @ (k1_zfmisc_1 @ X20)))),
% 0.67/0.90      inference('simplify', [status(thm)], ['28'])).
% 0.67/0.90  thf('30', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.67/0.90      inference('sup-', [status(thm)], ['27', '29'])).
% 0.67/0.90  thf(t63_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i,C:$i]:
% 0.67/0.90     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.67/0.90       ( r1_xboole_0 @ A @ C ) ))).
% 0.67/0.90  thf('31', plain,
% 0.67/0.90      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.67/0.90         (~ (r1_tarski @ X7 @ X8)
% 0.67/0.90          | ~ (r1_xboole_0 @ X8 @ X9)
% 0.67/0.90          | (r1_xboole_0 @ X7 @ X9))),
% 0.67/0.90      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.67/0.90  thf('32', plain,
% 0.67/0.90      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['30', '31'])).
% 0.67/0.90  thf('33', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.67/0.90      inference('sup-', [status(thm)], ['22', '32'])).
% 0.67/0.90  thf(t83_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.67/0.90  thf('34', plain,
% 0.67/0.90      (![X13 : $i, X14 : $i]:
% 0.67/0.90         (((k4_xboole_0 @ X13 @ X14) = (X13)) | ~ (r1_xboole_0 @ X13 @ X14))),
% 0.67/0.90      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.67/0.90  thf('35', plain,
% 0.67/0.90      (((k4_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (sk_B))),
% 0.67/0.90      inference('sup-', [status(thm)], ['33', '34'])).
% 0.67/0.90  thf(t36_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.67/0.90  thf('36', plain,
% 0.67/0.90      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.67/0.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.67/0.90  thf('37', plain,
% 0.67/0.90      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.67/0.90         (~ (r1_tarski @ X19 @ X20)
% 0.67/0.90          | (r2_hidden @ X19 @ X21)
% 0.67/0.90          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 0.67/0.90      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.67/0.90  thf('38', plain,
% 0.67/0.90      (![X19 : $i, X20 : $i]:
% 0.67/0.90         ((r2_hidden @ X19 @ (k1_zfmisc_1 @ X20)) | ~ (r1_tarski @ X19 @ X20))),
% 0.67/0.90      inference('simplify', [status(thm)], ['37'])).
% 0.67/0.90  thf('39', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.67/0.90      inference('sup-', [status(thm)], ['36', '38'])).
% 0.67/0.90  thf('40', plain,
% 0.67/0.90      (![X24 : $i, X25 : $i]:
% 0.67/0.90         (~ (r2_hidden @ X24 @ X25)
% 0.67/0.90          | (m1_subset_1 @ X24 @ X25)
% 0.67/0.90          | (v1_xboole_0 @ X25))),
% 0.67/0.90      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.67/0.90  thf('41', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.67/0.90          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['39', '40'])).
% 0.67/0.90  thf('42', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.67/0.90      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.67/0.90  thf('43', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 0.67/0.90      inference('clc', [status(thm)], ['41', '42'])).
% 0.67/0.90  thf('44', plain,
% 0.67/0.90      (![X27 : $i, X28 : $i]:
% 0.67/0.90         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.67/0.90          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.67/0.90      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.67/0.90  thf('45', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.67/0.90           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.90  thf('46', plain,
% 0.67/0.90      (((k3_subset_1 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (sk_B))),
% 0.67/0.90      inference('demod', [status(thm)], ['35', '45'])).
% 0.67/0.90  thf('47', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 0.67/0.90           = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.90  thf(t38_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.67/0.90       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.67/0.90  thf('48', plain,
% 0.67/0.90      (![X5 : $i, X6 : $i]:
% 0.67/0.90         (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ (k4_xboole_0 @ X6 @ X5)))),
% 0.67/0.90      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.67/0.90  thf('49', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         (~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 0.67/0.90             (k3_subset_1 @ X1 @ (k4_xboole_0 @ X1 @ X0)))
% 0.67/0.90          | ((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['47', '48'])).
% 0.67/0.90  thf('50', plain,
% 0.67/0.90      ((~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_B)
% 0.67/0.90        | ((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0)))),
% 0.67/0.90      inference('sup-', [status(thm)], ['46', '49'])).
% 0.67/0.90  thf('51', plain,
% 0.67/0.90      (![X3 : $i, X4 : $i]: (r1_tarski @ (k4_xboole_0 @ X3 @ X4) @ X3)),
% 0.67/0.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.67/0.90  thf('52', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.67/0.90      inference('demod', [status(thm)], ['50', '51'])).
% 0.67/0.90  thf(l32_xboole_1, axiom,
% 0.67/0.90    (![A:$i,B:$i]:
% 0.67/0.90     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.90  thf('53', plain,
% 0.67/0.90      (![X0 : $i, X1 : $i]:
% 0.67/0.90         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.67/0.90      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.67/0.90  thf('54', plain,
% 0.67/0.90      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_C_1))),
% 0.67/0.90      inference('sup-', [status(thm)], ['52', '53'])).
% 0.67/0.90  thf('55', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.67/0.90      inference('simplify', [status(thm)], ['54'])).
% 0.67/0.90  thf('56', plain, ($false), inference('demod', [status(thm)], ['14', '55'])).
% 0.67/0.90  
% 0.67/0.90  % SZS output end Refutation
% 0.67/0.90  
% 0.67/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
