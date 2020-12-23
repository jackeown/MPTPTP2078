%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BVUb9ZJSR9

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:01 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   61 (  85 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  413 ( 733 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    | ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
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

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ X19 )
      | ( r2_hidden @ X18 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('6',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['4','5'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X16 @ X15 )
      | ( r1_tarski @ X16 @ X14 )
      | ( X15
       != ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('8',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ X16 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_1 )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['10'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X10 @ X12 )
      | ( r1_tarski @ X10 @ ( k4_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_1 ) )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_subset_1 @ X21 @ X22 )
        = ( k4_xboole_0 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('17',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['10'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X8 @ X9 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('26',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['10'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,
    ( ( ( k2_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
      = ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('29',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X4 @ ( k2_xboole_0 @ X5 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
        | ( r1_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ sk_A @ sk_C_1 ) )
        | ( r1_xboole_0 @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_B )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('34',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C_1 )
   <= ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','20','21','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BVUb9ZJSR9
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:00:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.35/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.61  % Solved by: fo/fo7.sh
% 0.35/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.61  % done 199 iterations in 0.150s
% 0.35/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.61  % SZS output start Refutation
% 0.35/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.35/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.35/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.35/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.35/0.61  thf(t43_subset_1, conjecture,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.61       ( ![C:$i]:
% 0.35/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.61           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.35/0.61             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.35/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.61    (~( ![A:$i,B:$i]:
% 0.35/0.61        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.61          ( ![C:$i]:
% 0.35/0.61            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.61              ( ( r1_xboole_0 @ B @ C ) <=>
% 0.35/0.61                ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.35/0.61    inference('cnf.neg', [status(esa)], [t43_subset_1])).
% 0.35/0.61  thf('0', plain,
% 0.35/0.61      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.35/0.61        | ~ (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('1', plain,
% 0.35/0.61      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.35/0.61       ~ ((r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.35/0.61      inference('split', [status(esa)], ['0'])).
% 0.35/0.61  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(d2_subset_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( v1_xboole_0 @ A ) =>
% 0.35/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.35/0.61       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.35/0.61         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.35/0.61  thf('3', plain,
% 0.35/0.61      (![X18 : $i, X19 : $i]:
% 0.35/0.61         (~ (m1_subset_1 @ X18 @ X19)
% 0.35/0.61          | (r2_hidden @ X18 @ X19)
% 0.35/0.61          | (v1_xboole_0 @ X19))),
% 0.35/0.61      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.35/0.61  thf('4', plain,
% 0.35/0.61      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.35/0.61        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.35/0.61  thf(fc1_subset_1, axiom,
% 0.35/0.61    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.61  thf('5', plain, (![X25 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X25))),
% 0.35/0.61      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.35/0.61  thf('6', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.61      inference('clc', [status(thm)], ['4', '5'])).
% 0.35/0.61  thf(d1_zfmisc_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.35/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.35/0.61  thf('7', plain,
% 0.35/0.61      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.35/0.61         (~ (r2_hidden @ X16 @ X15)
% 0.35/0.61          | (r1_tarski @ X16 @ X14)
% 0.35/0.61          | ((X15) != (k1_zfmisc_1 @ X14)))),
% 0.35/0.61      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.35/0.61  thf('8', plain,
% 0.35/0.61      (![X14 : $i, X16 : $i]:
% 0.35/0.61         ((r1_tarski @ X16 @ X14) | ~ (r2_hidden @ X16 @ (k1_zfmisc_1 @ X14)))),
% 0.35/0.61      inference('simplify', [status(thm)], ['7'])).
% 0.35/0.61  thf('9', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.35/0.61      inference('sup-', [status(thm)], ['6', '8'])).
% 0.35/0.61  thf('10', plain,
% 0.35/0.61      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.35/0.61        | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf('11', plain,
% 0.35/0.61      (((r1_xboole_0 @ sk_B @ sk_C_1)) <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.35/0.61      inference('split', [status(esa)], ['10'])).
% 0.35/0.61  thf(t86_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.35/0.61       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.35/0.61  thf('12', plain,
% 0.35/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.61         (~ (r1_tarski @ X10 @ X11)
% 0.35/0.61          | ~ (r1_xboole_0 @ X10 @ X12)
% 0.35/0.61          | (r1_tarski @ X10 @ (k4_xboole_0 @ X11 @ X12)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.35/0.61  thf('13', plain,
% 0.35/0.61      ((![X0 : $i]:
% 0.35/0.61          ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_1))
% 0.35/0.61           | ~ (r1_tarski @ sk_B @ X0)))
% 0.35/0.61         <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.35/0.61  thf('14', plain,
% 0.35/0.61      (((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1)))
% 0.35/0.61         <= (((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.35/0.61      inference('sup-', [status(thm)], ['9', '13'])).
% 0.35/0.61  thf('15', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.35/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.61  thf(d5_subset_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.35/0.61       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.35/0.61  thf('16', plain,
% 0.35/0.61      (![X21 : $i, X22 : $i]:
% 0.35/0.61         (((k3_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))
% 0.35/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X21)))),
% 0.35/0.61      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.35/0.61  thf('17', plain,
% 0.35/0.61      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.61  thf('18', plain,
% 0.35/0.61      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.35/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.35/0.61      inference('split', [status(esa)], ['0'])).
% 0.35/0.61  thf('19', plain,
% 0.35/0.61      ((~ (r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_1)))
% 0.35/0.61         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.35/0.61  thf('20', plain,
% 0.35/0.61      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.35/0.61       ~ ((r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['14', '19'])).
% 0.35/0.61  thf('21', plain,
% 0.35/0.61      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.35/0.61       ((r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.35/0.61      inference('split', [status(esa)], ['10'])).
% 0.35/0.61  thf(t79_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.35/0.61  thf('22', plain,
% 0.35/0.61      (![X8 : $i, X9 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X8 @ X9) @ X9)),
% 0.35/0.61      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.35/0.61  thf(symmetry_r1_xboole_0, axiom,
% 0.35/0.61    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.35/0.61  thf('23', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.35/0.61      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.35/0.61  thf('24', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.35/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.35/0.61  thf('25', plain,
% 0.35/0.61      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['15', '16'])).
% 0.35/0.61  thf('26', plain,
% 0.35/0.61      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.35/0.61         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.35/0.61      inference('split', [status(esa)], ['10'])).
% 0.35/0.61  thf(t12_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i]:
% 0.35/0.61     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.35/0.61  thf('27', plain,
% 0.35/0.61      (![X2 : $i, X3 : $i]:
% 0.35/0.61         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.35/0.61      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.35/0.61  thf('28', plain,
% 0.35/0.61      ((((k2_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.35/0.61          = (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.35/0.61         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.61  thf(t70_xboole_1, axiom,
% 0.35/0.61    (![A:$i,B:$i,C:$i]:
% 0.35/0.61     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.35/0.61            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.35/0.61       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.35/0.61            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.35/0.61  thf('29', plain,
% 0.35/0.61      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.35/0.61         ((r1_xboole_0 @ X4 @ X5)
% 0.35/0.61          | ~ (r1_xboole_0 @ X4 @ (k2_xboole_0 @ X5 @ X7)))),
% 0.35/0.61      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.35/0.61  thf('30', plain,
% 0.35/0.61      ((![X0 : $i]:
% 0.35/0.61          (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.35/0.61           | (r1_xboole_0 @ X0 @ sk_B)))
% 0.35/0.61         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.35/0.61  thf('31', plain,
% 0.35/0.61      ((![X0 : $i]:
% 0.35/0.61          (~ (r1_xboole_0 @ X0 @ (k4_xboole_0 @ sk_A @ sk_C_1))
% 0.35/0.61           | (r1_xboole_0 @ X0 @ sk_B)))
% 0.35/0.61         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['25', '30'])).
% 0.35/0.61  thf('32', plain,
% 0.35/0.61      (((r1_xboole_0 @ sk_C_1 @ sk_B))
% 0.35/0.61         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['24', '31'])).
% 0.35/0.61  thf('33', plain,
% 0.35/0.61      (![X0 : $i, X1 : $i]:
% 0.35/0.61         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.35/0.61      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.35/0.61  thf('34', plain,
% 0.35/0.61      (((r1_xboole_0 @ sk_B @ sk_C_1))
% 0.35/0.61         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))))),
% 0.35/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.35/0.61  thf('35', plain,
% 0.35/0.61      ((~ (r1_xboole_0 @ sk_B @ sk_C_1)) <= (~ ((r1_xboole_0 @ sk_B @ sk_C_1)))),
% 0.35/0.61      inference('split', [status(esa)], ['0'])).
% 0.35/0.61  thf('36', plain,
% 0.35/0.61      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1))) | 
% 0.35/0.61       ((r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.35/0.61      inference('sup-', [status(thm)], ['34', '35'])).
% 0.35/0.61  thf('37', plain, ($false),
% 0.35/0.61      inference('sat_resolution*', [status(thm)], ['1', '20', '21', '36'])).
% 0.35/0.61  
% 0.35/0.61  % SZS output end Refutation
% 0.35/0.61  
% 0.35/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
