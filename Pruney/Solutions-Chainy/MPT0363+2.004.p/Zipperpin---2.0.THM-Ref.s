%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.brDFYhS3XF

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 173 expanded)
%              Number of leaves         :   27 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  541 (1375 expanded)
%              Number of equality atoms :   32 (  67 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t43_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( r1_xboole_0 @ B @ C )
            <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_subset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('4',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['5'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('10',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('18',plain,(
    ! [X14: $i] :
      ( r1_xboole_0 @ X14 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('23',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) )
      = sk_C_1 )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['10','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ sk_C_1 @ sk_B )
      = sk_C_1 )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = sk_B )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
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

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('34',plain,(
    ! [X27: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('35',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r1_tarski @ X20 @ X18 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('37',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['35','37'])).

thf(t33_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('39',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ( r1_tarski @ ( k4_xboole_0 @ X7 @ X9 ) @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t33_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k4_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['30','40'])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['4','41'])).

thf('43',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X15 @ X16 ) @ X16 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('46',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_C_1 ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( r1_xboole_0 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('52',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_1 )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['5'])).

thf('54',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['43','52','53'])).

thf('55',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['42','54'])).

thf('56',plain,
    ( $false
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['1','55'])).

thf('57',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['43','52'])).

thf('58',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.brDFYhS3XF
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:15:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 183 iterations in 0.072s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.53  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(t43_subset_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.20/0.53             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53          ( ![C:$i]:
% 0.20/0.53            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53              ( ( r1_xboole_0 @ B @ C ) <=>
% 0.20/0.53                ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t43_subset_1])).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.20/0.53        | ~ (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.20/0.53         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d5_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.53       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X25 : $i, X26 : $i]:
% 0.20/0.53         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.20/0.53          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.20/0.53        | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_B @ sk_C_1)) <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf(d7_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      ((((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0)))
% 0.20/0.53         <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf(t100_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X5 @ X6)
% 0.20/0.53           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_B @ sk_C_1) = (k5_xboole_0 @ sk_B @ k1_xboole_0)))
% 0.20/0.53         <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.53  thf(t79_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.20/0.53      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.53  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X5 @ X6)
% 0.20/0.53           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.20/0.53           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.53  thf('18', plain, (![X14 : $i]: (r1_xboole_0 @ X14 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i]:
% 0.20/0.53         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X5 @ X6)
% 0.20/0.53           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf(t3_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('23', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.53  thf('24', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_C_1 @ (k5_xboole_0 @ sk_B @ k1_xboole_0)) = (sk_C_1)))
% 0.20/0.53         <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['10', '25'])).
% 0.20/0.53  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_C_1 @ sk_B) = (sk_C_1)))
% 0.20/0.53         <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.20/0.53      inference('demod', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.20/0.53      inference('demod', [status(thm)], ['17', '24'])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((((k4_xboole_0 @ sk_B @ sk_C_1) = (sk_B)))
% 0.20/0.53         <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(d2_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.53       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.53         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X22 @ X23)
% 0.20/0.53          | (r2_hidden @ X22 @ X23)
% 0.20/0.53          | (v1_xboole_0 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.53        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf(fc1_subset_1, axiom,
% 0.20/0.53    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.53  thf('34', plain, (![X27 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.53  thf('35', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.53      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf(d1_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X20 @ X19)
% 0.20/0.53          | (r1_tarski @ X20 @ X18)
% 0.20/0.53          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X18 : $i, X20 : $i]:
% 0.20/0.53         ((r1_tarski @ X20 @ X18) | ~ (r2_hidden @ X20 @ (k1_zfmisc_1 @ X18)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.53  thf('38', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['35', '37'])).
% 0.20/0.53  thf(t33_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) =>
% 0.20/0.53       ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X7 @ X8)
% 0.20/0.53          | (r1_tarski @ (k4_xboole_0 @ X7 @ X9) @ (k4_xboole_0 @ X8 @ X9)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t33_xboole_1])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ (k4_xboole_0 @ sk_A @ X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1)))
% 0.20/0.53         <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['30', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.20/0.53         <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.20/0.53      inference('sup+', [status(thm)], ['4', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.20/0.53       ~ ((r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X15 : $i, X16 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X15 @ X16) @ X16)),
% 0.20/0.53      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.53  thf('46', plain, ((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_C_1)),
% 0.20/0.53      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.20/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf(t63_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.20/0.53       ( r1_xboole_0 @ A @ C ) ))).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X11 @ X12)
% 0.20/0.53          | ~ (r1_xboole_0 @ X12 @ X13)
% 0.20/0.53          | (r1_xboole_0 @ X11 @ X13))),
% 0.20/0.53      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      ((![X0 : $i]:
% 0.20/0.53          ((r1_xboole_0 @ sk_B @ X0)
% 0.20/0.53           | ~ (r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ X0)))
% 0.20/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_B @ sk_C_1))
% 0.20/0.53         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '49'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      ((~ (r1_xboole_0 @ sk_B @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['0'])).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_B @ sk_C_1)) | 
% 0.20/0.53       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      (((r1_xboole_0 @ sk_B @ sk_C_1)) | 
% 0.20/0.53       ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['5'])).
% 0.20/0.53  thf('54', plain, (((r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['43', '52', '53'])).
% 0.20/0.53  thf('55', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['42', '54'])).
% 0.20/0.53  thf('56', plain,
% 0.20/0.53      (($false) <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.20/0.53      inference('demod', [status(thm)], ['1', '55'])).
% 0.20/0.53  thf('57', plain, (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['43', '52'])).
% 0.20/0.53  thf('58', plain, ($false),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['56', '57'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
