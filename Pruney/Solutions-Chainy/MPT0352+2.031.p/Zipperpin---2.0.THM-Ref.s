%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cOzNXbvTso

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:12 EST 2020

% Result     : Theorem 0.88s
% Output     : Refutation 0.88s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 170 expanded)
%              Number of leaves         :   23 (  56 expanded)
%              Depth                    :   17
%              Number of atoms          :  544 (1686 expanded)
%              Number of equality atoms :   16 (  38 expanded)
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

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
   <= ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ( r2_hidden @ X29 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X34: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('7',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['5','6'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X27 @ X26 )
      | ( r1_tarski @ X27 @ X25 )
      | ( X26
       != ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X25: $i,X27: $i] :
      ( ( r1_tarski @ X27 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('15',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X6 @ X8 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ sk_B )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('20',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X21 @ X23 )
      | ( r1_tarski @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('22',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
        | ~ ( r1_tarski @ sk_B @ X0 ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X32: $i,X33: $i] :
      ( ( ( k3_subset_1 @ X32 @ X33 )
        = ( k4_xboole_0 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('26',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('28',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('30',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_subset_1 @ sk_A @ sk_C_1 ) )
    = ( k3_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ sk_A ) )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','30'])).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k4_xboole_0 @ X19 @ X20 ) )
      = ( k3_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ X6 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['2','37'])).

thf('39',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['1','38'])).

thf('40',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_1 )
    = ( k4_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('41',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['11'])).

thf('42',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['11'])).

thf('43',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','37','42'])).

thf('44',plain,(
    r1_tarski @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['41','43'])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('45',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ( r1_tarski @ ( k4_xboole_0 @ X16 @ X15 ) @ ( k4_xboole_0 @ X16 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ ( k4_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['40','46'])).

thf('48',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('49',plain,(
    r1_tarski @ ( k3_subset_1 @ sk_A @ sk_C_1 ) @ ( k3_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    $false ),
    inference(demod,[status(thm)],['39','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cOzNXbvTso
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.88/1.06  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.88/1.06  % Solved by: fo/fo7.sh
% 0.88/1.06  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.88/1.06  % done 1198 iterations in 0.610s
% 0.88/1.06  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.88/1.06  % SZS output start Refutation
% 0.88/1.06  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.88/1.06  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.88/1.06  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.88/1.06  thf(sk_A_type, type, sk_A: $i).
% 0.88/1.06  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.88/1.06  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.88/1.06  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.88/1.06  thf(sk_B_type, type, sk_B: $i).
% 0.88/1.06  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.88/1.06  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.88/1.06  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.88/1.06  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.88/1.06  thf(t31_subset_1, conjecture,
% 0.88/1.06    (![A:$i,B:$i]:
% 0.88/1.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.06       ( ![C:$i]:
% 0.88/1.06         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.06           ( ( r1_tarski @ B @ C ) <=>
% 0.88/1.06             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.88/1.06  thf(zf_stmt_0, negated_conjecture,
% 0.88/1.06    (~( ![A:$i,B:$i]:
% 0.88/1.06        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.06          ( ![C:$i]:
% 0.88/1.06            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.06              ( ( r1_tarski @ B @ C ) <=>
% 0.88/1.06                ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.88/1.06    inference('cnf.neg', [status(esa)], [t31_subset_1])).
% 0.88/1.06  thf('0', plain,
% 0.88/1.06      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06           (k3_subset_1 @ sk_A @ sk_B))
% 0.88/1.06        | ~ (r1_tarski @ sk_B @ sk_C_1))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('1', plain,
% 0.88/1.06      ((~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06           (k3_subset_1 @ sk_A @ sk_B)))
% 0.88/1.06         <= (~
% 0.88/1.06             ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.88/1.06      inference('split', [status(esa)], ['0'])).
% 0.88/1.06  thf('2', plain,
% 0.88/1.06      (~
% 0.88/1.06       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06         (k3_subset_1 @ sk_A @ sk_B))) | 
% 0.88/1.06       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.88/1.06      inference('split', [status(esa)], ['0'])).
% 0.88/1.06  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(d2_subset_1, axiom,
% 0.88/1.06    (![A:$i,B:$i]:
% 0.88/1.06     ( ( ( v1_xboole_0 @ A ) =>
% 0.88/1.06         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.88/1.06       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.88/1.06         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.88/1.06  thf('4', plain,
% 0.88/1.06      (![X29 : $i, X30 : $i]:
% 0.88/1.06         (~ (m1_subset_1 @ X29 @ X30)
% 0.88/1.06          | (r2_hidden @ X29 @ X30)
% 0.88/1.06          | (v1_xboole_0 @ X30))),
% 0.88/1.06      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.88/1.06  thf('5', plain,
% 0.88/1.06      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.88/1.06        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['3', '4'])).
% 0.88/1.06  thf(fc1_subset_1, axiom,
% 0.88/1.06    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.88/1.06  thf('6', plain, (![X34 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X34))),
% 0.88/1.06      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.88/1.06  thf('7', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.88/1.06      inference('clc', [status(thm)], ['5', '6'])).
% 0.88/1.06  thf(d1_zfmisc_1, axiom,
% 0.88/1.06    (![A:$i,B:$i]:
% 0.88/1.06     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.88/1.06       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.88/1.06  thf('8', plain,
% 0.88/1.06      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.88/1.06         (~ (r2_hidden @ X27 @ X26)
% 0.88/1.06          | (r1_tarski @ X27 @ X25)
% 0.88/1.06          | ((X26) != (k1_zfmisc_1 @ X25)))),
% 0.88/1.06      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.88/1.06  thf('9', plain,
% 0.88/1.06      (![X25 : $i, X27 : $i]:
% 0.88/1.06         ((r1_tarski @ X27 @ X25) | ~ (r2_hidden @ X27 @ (k1_zfmisc_1 @ X25)))),
% 0.88/1.06      inference('simplify', [status(thm)], ['8'])).
% 0.88/1.06  thf('10', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.88/1.06      inference('sup-', [status(thm)], ['7', '9'])).
% 0.88/1.06  thf('11', plain,
% 0.88/1.06      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06         (k3_subset_1 @ sk_A @ sk_B))
% 0.88/1.06        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('12', plain,
% 0.88/1.06      (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06         (k3_subset_1 @ sk_A @ sk_B)))
% 0.88/1.06         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.88/1.06      inference('split', [status(esa)], ['11'])).
% 0.88/1.06  thf('13', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf(d5_subset_1, axiom,
% 0.88/1.06    (![A:$i,B:$i]:
% 0.88/1.06     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.88/1.06       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.88/1.06  thf('14', plain,
% 0.88/1.06      (![X32 : $i, X33 : $i]:
% 0.88/1.06         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 0.88/1.06          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.88/1.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.88/1.06  thf('15', plain,
% 0.88/1.06      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.88/1.06      inference('sup-', [status(thm)], ['13', '14'])).
% 0.88/1.06  thf(t106_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.88/1.06       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.88/1.06  thf('16', plain,
% 0.88/1.06      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.88/1.06         ((r1_xboole_0 @ X6 @ X8)
% 0.88/1.06          | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.88/1.06      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.88/1.06  thf('17', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_B))
% 0.88/1.06          | (r1_xboole_0 @ X0 @ sk_B))),
% 0.88/1.06      inference('sup-', [status(thm)], ['15', '16'])).
% 0.88/1.06  thf('18', plain,
% 0.88/1.06      (((r1_xboole_0 @ (k3_subset_1 @ sk_A @ sk_C_1) @ sk_B))
% 0.88/1.06         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['12', '17'])).
% 0.88/1.06  thf(symmetry_r1_xboole_0, axiom,
% 0.88/1.06    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.88/1.06  thf('19', plain,
% 0.88/1.06      (![X2 : $i, X3 : $i]:
% 0.88/1.06         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.88/1.06      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.88/1.06  thf('20', plain,
% 0.88/1.06      (((r1_xboole_0 @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.88/1.06         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['18', '19'])).
% 0.88/1.06  thf(t86_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.88/1.06       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.88/1.06  thf('21', plain,
% 0.88/1.06      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X21 @ X22)
% 0.88/1.06          | ~ (r1_xboole_0 @ X21 @ X23)
% 0.88/1.06          | (r1_tarski @ X21 @ (k4_xboole_0 @ X22 @ X23)))),
% 0.88/1.06      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.88/1.06  thf('22', plain,
% 0.88/1.06      ((![X0 : $i]:
% 0.88/1.06          ((r1_tarski @ sk_B @ 
% 0.88/1.06            (k4_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_1)))
% 0.88/1.06           | ~ (r1_tarski @ sk_B @ X0)))
% 0.88/1.06         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['20', '21'])).
% 0.88/1.06  thf('23', plain,
% 0.88/1.06      (((r1_tarski @ sk_B @ 
% 0.88/1.06         (k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))))
% 0.88/1.06         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['10', '22'])).
% 0.88/1.06  thf('24', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.88/1.06      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.88/1.06  thf('25', plain,
% 0.88/1.06      (![X32 : $i, X33 : $i]:
% 0.88/1.06         (((k3_subset_1 @ X32 @ X33) = (k4_xboole_0 @ X32 @ X33))
% 0.88/1.06          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X32)))),
% 0.88/1.06      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.88/1.06  thf('26', plain,
% 0.88/1.06      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.88/1.06      inference('sup-', [status(thm)], ['24', '25'])).
% 0.88/1.06  thf(t48_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i]:
% 0.88/1.06     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.88/1.06  thf('27', plain,
% 0.88/1.06      (![X19 : $i, X20 : $i]:
% 0.88/1.06         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.88/1.06           = (k3_xboole_0 @ X19 @ X20))),
% 0.88/1.06      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.88/1.06  thf('28', plain,
% 0.88/1.06      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.88/1.06         = (k3_xboole_0 @ sk_A @ sk_C_1))),
% 0.88/1.06      inference('sup+', [status(thm)], ['26', '27'])).
% 0.88/1.06  thf(commutativity_k3_xboole_0, axiom,
% 0.88/1.06    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.88/1.06  thf('29', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.88/1.06      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.88/1.06  thf('30', plain,
% 0.88/1.06      (((k4_xboole_0 @ sk_A @ (k3_subset_1 @ sk_A @ sk_C_1))
% 0.88/1.06         = (k3_xboole_0 @ sk_C_1 @ sk_A))),
% 0.88/1.06      inference('demod', [status(thm)], ['28', '29'])).
% 0.88/1.06  thf('31', plain,
% 0.88/1.06      (((r1_tarski @ sk_B @ (k3_xboole_0 @ sk_C_1 @ sk_A)))
% 0.88/1.06         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.88/1.06      inference('demod', [status(thm)], ['23', '30'])).
% 0.88/1.06  thf('32', plain,
% 0.88/1.06      (![X19 : $i, X20 : $i]:
% 0.88/1.06         ((k4_xboole_0 @ X19 @ (k4_xboole_0 @ X19 @ X20))
% 0.88/1.06           = (k3_xboole_0 @ X19 @ X20))),
% 0.88/1.06      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.88/1.06  thf('33', plain,
% 0.88/1.06      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.88/1.06         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ X6 @ (k4_xboole_0 @ X7 @ X8)))),
% 0.88/1.06      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.88/1.06  thf('34', plain,
% 0.88/1.06      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X1))),
% 0.88/1.06      inference('sup-', [status(thm)], ['32', '33'])).
% 0.88/1.06  thf('35', plain,
% 0.88/1.06      (((r1_tarski @ sk_B @ sk_C_1))
% 0.88/1.06         <= (((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06               (k3_subset_1 @ sk_A @ sk_B))))),
% 0.88/1.06      inference('sup-', [status(thm)], ['31', '34'])).
% 0.88/1.06  thf('36', plain,
% 0.88/1.06      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.88/1.06      inference('split', [status(esa)], ['0'])).
% 0.88/1.06  thf('37', plain,
% 0.88/1.06      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.88/1.06       ~
% 0.88/1.06       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06         (k3_subset_1 @ sk_A @ sk_B)))),
% 0.88/1.06      inference('sup-', [status(thm)], ['35', '36'])).
% 0.88/1.06  thf('38', plain,
% 0.88/1.06      (~
% 0.88/1.06       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06         (k3_subset_1 @ sk_A @ sk_B)))),
% 0.88/1.06      inference('sat_resolution*', [status(thm)], ['2', '37'])).
% 0.88/1.06  thf('39', plain,
% 0.88/1.06      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06          (k3_subset_1 @ sk_A @ sk_B))),
% 0.88/1.06      inference('simpl_trail', [status(thm)], ['1', '38'])).
% 0.88/1.06  thf('40', plain,
% 0.88/1.06      (((k3_subset_1 @ sk_A @ sk_C_1) = (k4_xboole_0 @ sk_A @ sk_C_1))),
% 0.88/1.06      inference('sup-', [status(thm)], ['24', '25'])).
% 0.88/1.06  thf('41', plain,
% 0.88/1.06      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.88/1.06      inference('split', [status(esa)], ['11'])).
% 0.88/1.06  thf('42', plain,
% 0.88/1.06      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.88/1.06       ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ 
% 0.88/1.06         (k3_subset_1 @ sk_A @ sk_B)))),
% 0.88/1.06      inference('split', [status(esa)], ['11'])).
% 0.88/1.06  thf('43', plain, (((r1_tarski @ sk_B @ sk_C_1))),
% 0.88/1.06      inference('sat_resolution*', [status(thm)], ['2', '37', '42'])).
% 0.88/1.06  thf('44', plain, ((r1_tarski @ sk_B @ sk_C_1)),
% 0.88/1.06      inference('simpl_trail', [status(thm)], ['41', '43'])).
% 0.88/1.06  thf(t34_xboole_1, axiom,
% 0.88/1.06    (![A:$i,B:$i,C:$i]:
% 0.88/1.06     ( ( r1_tarski @ A @ B ) =>
% 0.88/1.06       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 0.88/1.06  thf('45', plain,
% 0.88/1.06      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.88/1.06         (~ (r1_tarski @ X14 @ X15)
% 0.88/1.06          | (r1_tarski @ (k4_xboole_0 @ X16 @ X15) @ (k4_xboole_0 @ X16 @ X14)))),
% 0.88/1.06      inference('cnf', [status(esa)], [t34_xboole_1])).
% 0.88/1.06  thf('46', plain,
% 0.88/1.06      (![X0 : $i]:
% 0.88/1.06         (r1_tarski @ (k4_xboole_0 @ X0 @ sk_C_1) @ (k4_xboole_0 @ X0 @ sk_B))),
% 0.88/1.06      inference('sup-', [status(thm)], ['44', '45'])).
% 0.88/1.06  thf('47', plain,
% 0.88/1.06      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.88/1.06      inference('sup+', [status(thm)], ['40', '46'])).
% 0.88/1.06  thf('48', plain,
% 0.88/1.06      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 0.88/1.06      inference('sup-', [status(thm)], ['13', '14'])).
% 0.88/1.06  thf('49', plain,
% 0.88/1.06      ((r1_tarski @ (k3_subset_1 @ sk_A @ sk_C_1) @ (k3_subset_1 @ sk_A @ sk_B))),
% 0.88/1.06      inference('demod', [status(thm)], ['47', '48'])).
% 0.88/1.06  thf('50', plain, ($false), inference('demod', [status(thm)], ['39', '49'])).
% 0.88/1.06  
% 0.88/1.06  % SZS output end Refutation
% 0.88/1.06  
% 0.88/1.07  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
