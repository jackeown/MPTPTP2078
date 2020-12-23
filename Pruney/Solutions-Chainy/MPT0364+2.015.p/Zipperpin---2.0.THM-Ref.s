%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eTs8ygK2Sg

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 112 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  402 ( 965 expanded)
%              Number of equality atoms :   16 (  21 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ! [X25: $i,X26: $i] :
      ( ( ( k3_subset_1 @ X25 @ X26 )
        = ( k4_xboole_0 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_xboole_0 @ X14 @ ( k4_xboole_0 @ X16 @ X15 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) )
      | ~ ( r1_xboole_0 @ X9 @ ( k4_xboole_0 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t81_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      | ( r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) )
    = sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6 = k1_xboole_0 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('26',plain,
    ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ sk_C_1 ) @ sk_A )
    | ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
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

thf('28',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('29',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('30',plain,(
    ! [X27: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('31',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['29','30'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('32',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( r1_tarski @ X20 @ X18 )
      | ( X19
       != ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('33',plain,(
    ! [X18: $i,X20: $i] :
      ( ( r1_tarski @ X20 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['31','33'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['26','36'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['14','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.eTs8ygK2Sg
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:26:57 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 152 iterations in 0.060s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(t44_subset_1, conjecture,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ![C:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51           ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.20/0.51             ( r1_tarski @ B @ C ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i]:
% 0.20/0.51        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51          ( ![C:$i]:
% 0.20/0.51            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51              ( ( r1_xboole_0 @ B @ ( k3_subset_1 @ A @ C ) ) <=>
% 0.20/0.51                ( r1_tarski @ B @ C ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t44_subset_1])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.20/0.51        | ~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.20/0.51       ~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('3', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d5_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i]:
% 0.20/0.51         (((k3_subset_1 @ X25 @ X26) = (k4_xboole_0 @ X25 @ X26))
% 0.20/0.51          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X25)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ sk_C_1)
% 0.20/0.51        | (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.20/0.51      inference('split', [status(esa)], ['6'])).
% 0.20/0.51  thf(t85_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.20/0.51  thf('8', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X14 @ X15)
% 0.20/0.51          | (r1_xboole_0 @ X14 @ (k4_xboole_0 @ X16 @ X15)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1)))
% 0.20/0.51         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.20/0.51         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['5', '9'])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((~ (r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.20/0.51         <= (~ ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.20/0.51       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain, (~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['2', '12'])).
% 0.20/0.51  thf('14', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['1', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.20/0.51         <= (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.20/0.51      inference('split', [status(esa)], ['6'])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.20/0.51       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.20/0.51      inference('split', [status(esa)], ['6'])).
% 0.20/0.51  thf('17', plain, (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['2', '12', '16'])).
% 0.20/0.51  thf('18', plain, ((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))),
% 0.20/0.51      inference('simpl_trail', [status(thm)], ['15', '17'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.51  thf(t81_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r1_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.20/0.51       ( r1_xboole_0 @ B @ ( k4_xboole_0 @ A @ C ) ) ))).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.51         ((r1_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X10))
% 0.20/0.51          | ~ (r1_xboole_0 @ X9 @ (k4_xboole_0 @ X8 @ X10)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t81_xboole_1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.20/0.51          | (r1_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_C_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain, ((r1_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.51  thf(t83_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i]:
% 0.20/0.51         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (((k4_xboole_0 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C_1)) = (sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf(t38_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.20/0.51       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (((X6) = (k1_xboole_0)) | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X6)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((~ (r1_tarski @ (k4_xboole_0 @ sk_B @ sk_C_1) @ sk_A)
% 0.20/0.51        | ((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d2_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X22 : $i, X23 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X22 @ X23)
% 0.20/0.51          | (r2_hidden @ X22 @ X23)
% 0.20/0.51          | (v1_xboole_0 @ X23))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.51        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf(fc1_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.51  thf('30', plain, (![X27 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X27))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.20/0.51  thf('31', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('clc', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf(d1_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X20 @ X19)
% 0.20/0.51          | (r1_tarski @ X20 @ X18)
% 0.20/0.51          | ((X19) != (k1_zfmisc_1 @ X18)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X18 : $i, X20 : $i]:
% 0.20/0.51         ((r1_tarski @ X20 @ X18) | ~ (r2_hidden @ X20 @ (k1_zfmisc_1 @ X18)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.51  thf('34', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '33'])).
% 0.20/0.51  thf(t109_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (r1_tarski @ X3 @ X4) | (r1_tarski @ (k4_xboole_0 @ X3 @ X5) @ X4))),
% 0.20/0.51      inference('cnf', [status(esa)], [t109_xboole_1])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain, (((k4_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['26', '36'])).
% 0.20/0.51  thf(l32_xboole_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 0.20/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_B @ sk_C_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.20/0.51      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.51  thf('41', plain, ($false), inference('demod', [status(thm)], ['14', '40'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
