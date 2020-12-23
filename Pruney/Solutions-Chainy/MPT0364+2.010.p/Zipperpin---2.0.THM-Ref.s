%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RcV7VQRbgF

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:03 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 119 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   15
%              Number of atoms          :  449 (1021 expanded)
%              Number of equality atoms :   20 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X13 @ ( k4_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_xboole_0 @ X14 @ ( k4_xboole_0 @ X13 @ X15 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 )
      | ( r1_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('36',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ ( k4_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) )
      = ( k4_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','40'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('43',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['14','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.16  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RcV7VQRbgF
% 0.16/0.37  % Computer   : n019.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 10:56:53 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 278 iterations in 0.131s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.41/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.41/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(t44_subset_1, conjecture,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.61       ( ![C:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.61           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.41/0.61             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i]:
% 0.41/0.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.61          ( ![C:$i]:
% 0.41/0.61            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.61              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.41/0.61                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.41/0.61        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.41/0.61       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('3', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d5_subset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X27 : $i, X28 : $i]:
% 0.41/0.61         (((k3_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))
% 0.41/0.61          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X27)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (((r1_tarski @ sk_B @ sk_C_1)
% 0.41/0.61        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['6'])).
% 0.41/0.61  thf(t85_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X16 @ X17)
% 0.41/0.61          | (r1_xboole_0 @ X16 @ (k4_xboole_0 @ X18 @ X17)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 0.41/0.61         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.41/0.61         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['5', '9'])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.41/0.61         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.41/0.61       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.61  thf('13', plain, (~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.41/0.61  thf('14', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.41/0.61         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.41/0.61      inference('split', [status(esa)], ['6'])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.41/0.61       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.41/0.61      inference('split', [status(esa)], ['6'])).
% 0.41/0.61  thf('17', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['2', '12', '16'])).
% 0.41/0.61  thf('18', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['15', '17'])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.61  thf(t81_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.41/0.61       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.41/0.61         ((r1_xboole_0 @ X13 @ (k4_xboole_0 @ X14 @ X15))
% 0.41/0.61          | ~ (r1_xboole_0 @ X14 @ (k4_xboole_0 @ X13 @ X15)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.41/0.61          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.61  thf('22', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['18', '21'])).
% 0.41/0.61  thf('23', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d2_subset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( v1_xboole_0 @ A ) =>
% 0.41/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.41/0.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X24 @ X25)
% 0.41/0.61          | (r2_hidden @ X24 @ X25)
% 0.41/0.61          | (v1_xboole_0 @ X25))),
% 0.41/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.61        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['23', '24'])).
% 0.41/0.61  thf(fc1_subset_1, axiom,
% 0.41/0.61    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.61  thf('26', plain, (![X29 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X29))),
% 0.41/0.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.41/0.61  thf('27', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.61      inference('clc', [status(thm)], ['25', '26'])).
% 0.41/0.61  thf(d1_zfmisc_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.41/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X22 @ X21)
% 0.41/0.61          | (r1_tarski @ X22 @ X20)
% 0.41/0.61          | ((X21) != (k1_zfmisc_1 @ X20)))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      (![X20 : $i, X22 : $i]:
% 0.41/0.61         ((r1_tarski @ X22 @ X20) | ~ (r2_hidden @ X22 @ (k1_zfmisc_1 @ X20)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['28'])).
% 0.41/0.61  thf('30', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.41/0.61      inference('sup-', [status(thm)], ['27', '29'])).
% 0.41/0.61  thf(t63_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.41/0.61       ( r1_xboole_0 @ A @ C ) ))).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X10 @ X11)
% 0.41/0.61          | ~ (r1_xboole_0 @ X11 @ X12)
% 0.41/0.61          | (r1_xboole_0 @ X10 @ X12))),
% 0.41/0.61      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      (![X0 : $i]: ((r1_xboole_0 @ sk_B @ X0) | ~ (r1_xboole_0 @ sk_A @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['30', '31'])).
% 0.41/0.61  thf('33', plain, ((r1_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['22', '32'])).
% 0.41/0.61  thf(d7_xboole_0, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.41/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      (((k3_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (k1_xboole_0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.61  thf(t48_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (![X8 : $i, X9 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.41/0.61           = (k3_xboole_0 @ X8 @ X9))),
% 0.41/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X8 : $i, X9 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ X8 @ (k4_xboole_0 @ X8 @ X9))
% 0.41/0.61           = (k3_xboole_0 @ X8 @ X9))),
% 0.41/0.61      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.41/0.61           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.41/0.61      inference('sup+', [status(thm)], ['36', '37'])).
% 0.41/0.61  thf(t47_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      (![X6 : $i, X7 : $i]:
% 0.41/0.61         ((k4_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7))
% 0.41/0.61           = (k4_xboole_0 @ X6 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 0.41/0.61           = (k4_xboole_0 @ X1 @ X0))),
% 0.41/0.61      inference('sup+', [status(thm)], ['38', '39'])).
% 0.41/0.61  thf('41', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.41/0.61      inference('demod', [status(thm)], ['35', '40'])).
% 0.41/0.61  thf(l32_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      (![X3 : $i, X4 : $i]:
% 0.41/0.61         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.41/0.61  thf('43', plain,
% 0.41/0.61      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.61  thf('44', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.41/0.61      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.61  thf('45', plain, ($false), inference('demod', [status(thm)], ['14', '44'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
