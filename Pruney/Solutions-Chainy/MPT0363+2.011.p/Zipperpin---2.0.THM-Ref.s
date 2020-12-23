%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yQBdQHMuED

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 161 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  532 (1606 expanded)
%              Number of equality atoms :    8 (  15 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
   <= ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
    | ~ ( r1_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k3_subset_1 @ X29 @ X30 )
        = ( k4_xboole_0 @ X29 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_3 )
    = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( r2_hidden @ X8 @ X6 )
      | ( X7
       != ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X5: $i,X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ ( k4_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X10 )
      | ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X10 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_C_3 @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['5','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('22',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
    | ( r1_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['22'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
        | ~ ( r2_hidden @ X0 @ sk_B ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
        | ( r1_xboole_0 @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k3_subset_1 @ sk_A @ sk_C_3 ) )
        | ( r1_xboole_0 @ sk_B @ X0 ) )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_3 )
   <= ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['20','29'])).

thf('31',plain,
    ( ~ ( r1_xboole_0 @ sk_B @ sk_C_3 )
   <= ~ ( r1_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_3 )
    | ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('38',plain,(
    ! [X31: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('39',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('40',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X24 @ X23 )
      | ( r1_tarski @ X24 @ X22 )
      | ( X23
       != ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('41',plain,(
    ! [X22: $i,X24: $i] :
      ( ( r1_tarski @ X24 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( k1_zfmisc_1 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_3 )
   <= ( r1_xboole_0 @ sk_B @ sk_C_3 ) ),
    inference(split,[status(esa)],['22'])).

thf('44',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_C_3 )
    | ( r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ) ),
    inference(split,[status(esa)],['22'])).

thf('45',plain,(
    r1_xboole_0 @ sk_B @ sk_C_3 ),
    inference('sat_resolution*',[status(thm)],['2','32','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ sk_C_3 ),
    inference(simpl_trail,[status(thm)],['43','45'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X18 )
      | ( r1_tarski @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C_3 ) )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C_3 )
    = ( k4_xboole_0 @ sk_A @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('51',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C_3 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['34','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yQBdQHMuED
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:59:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.55  % Solved by: fo/fo7.sh
% 0.21/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.55  % done 195 iterations in 0.108s
% 0.21/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.55  % SZS output start Refutation
% 0.21/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.55  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.21/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.55  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.21/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.55  thf(t43_subset_1, conjecture,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ![C:$i]:
% 0.21/0.55         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.21/0.55             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.21/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.55    (~( ![A:$i,B:$i]:
% 0.21/0.55        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55          ( ![C:$i]:
% 0.21/0.55            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55              ( ( r1_xboole_0 @ B @ C ) <=>
% 0.21/0.55                ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ) )),
% 0.21/0.55    inference('cnf.neg', [status(esa)], [t43_subset_1])).
% 0.21/0.55  thf('0', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))
% 0.21/0.55        | ~ (r1_xboole_0 @ sk_B @ sk_C_3))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('1', plain,
% 0.21/0.55      ((~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3)))
% 0.21/0.55         <= (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('2', plain,
% 0.21/0.55      (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))) | 
% 0.21/0.55       ~ ((r1_xboole_0 @ sk_B @ sk_C_3))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('3', plain, ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d5_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.55       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.21/0.55  thf('4', plain,
% 0.21/0.55      (![X29 : $i, X30 : $i]:
% 0.21/0.55         (((k3_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))
% 0.21/0.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X29)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.21/0.55  thf('5', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_C_3) = (k4_xboole_0 @ sk_A @ sk_C_3))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.55  thf(t3_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.55  thf('6', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf('7', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf(d5_xboole_0, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.21/0.55       ( ![D:$i]:
% 0.21/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.55           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.21/0.55  thf('8', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X8 @ X7)
% 0.21/0.55          | ~ (r2_hidden @ X8 @ X6)
% 0.21/0.55          | ((X7) != (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.21/0.55  thf('9', plain,
% 0.21/0.55      (![X5 : $i, X6 : $i, X8 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X8 @ X6)
% 0.21/0.55          | ~ (r2_hidden @ X8 @ (k4_xboole_0 @ X5 @ X6)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.55  thf('10', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X2)
% 0.21/0.55          | ~ (r2_hidden @ (sk_C_1 @ X2 @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['7', '9'])).
% 0.21/0.55  thf('11', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.21/0.55          | (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['6', '10'])).
% 0.21/0.55  thf('12', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)),
% 0.21/0.55      inference('simplify', [status(thm)], ['11'])).
% 0.21/0.55  thf('13', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf('14', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X11))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf('15', plain,
% 0.21/0.55      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X12 @ X10)
% 0.21/0.55          | ~ (r2_hidden @ X12 @ X13)
% 0.21/0.55          | ~ (r1_xboole_0 @ X10 @ X13))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf('16', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.55          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.55          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('17', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.55          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.55          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.55  thf('18', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]:
% 0.21/0.55         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.55  thf('19', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['12', '18'])).
% 0.21/0.55  thf('20', plain, ((r1_xboole_0 @ sk_C_3 @ (k3_subset_1 @ sk_A @ sk_C_3))),
% 0.21/0.55      inference('sup+', [status(thm)], ['5', '19'])).
% 0.21/0.55  thf('21', plain,
% 0.21/0.55      (![X10 : $i, X11 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X10 @ X11) | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10))),
% 0.21/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.55  thf('22', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))
% 0.21/0.55        | (r1_xboole_0 @ sk_B @ sk_C_3))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf('23', plain,
% 0.21/0.55      (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.21/0.55      inference('split', [status(esa)], ['22'])).
% 0.21/0.55  thf(d3_tarski, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.55  thf('24', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.55          | (r2_hidden @ X0 @ X2)
% 0.21/0.55          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.55      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.55  thf('25', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          ((r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_C_3))
% 0.21/0.55           | ~ (r2_hidden @ X0 @ sk_B)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.55  thf('26', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          ((r1_xboole_0 @ sk_B @ X0)
% 0.21/0.55           | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ (k3_subset_1 @ sk_A @ sk_C_3))))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['21', '25'])).
% 0.21/0.55  thf('27', plain,
% 0.21/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.55         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.55          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.55          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 0.21/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.55  thf('28', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          ((r1_xboole_0 @ sk_B @ X0)
% 0.21/0.55           | ~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_3))
% 0.21/0.55           | (r1_xboole_0 @ sk_B @ X0)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.55  thf('29', plain,
% 0.21/0.55      ((![X0 : $i]:
% 0.21/0.55          (~ (r1_xboole_0 @ X0 @ (k3_subset_1 @ sk_A @ sk_C_3))
% 0.21/0.55           | (r1_xboole_0 @ sk_B @ X0)))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.21/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.21/0.55  thf('30', plain,
% 0.21/0.55      (((r1_xboole_0 @ sk_B @ sk_C_3))
% 0.21/0.55         <= (((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))))),
% 0.21/0.55      inference('sup-', [status(thm)], ['20', '29'])).
% 0.21/0.55  thf('31', plain,
% 0.21/0.55      ((~ (r1_xboole_0 @ sk_B @ sk_C_3)) <= (~ ((r1_xboole_0 @ sk_B @ sk_C_3)))),
% 0.21/0.55      inference('split', [status(esa)], ['0'])).
% 0.21/0.55  thf('32', plain,
% 0.21/0.55      (((r1_xboole_0 @ sk_B @ sk_C_3)) | 
% 0.21/0.55       ~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.55  thf('33', plain, (~ ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3)))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['2', '32'])).
% 0.21/0.55  thf('34', plain, (~ (r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.21/0.55  thf('35', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.55  thf(d2_subset_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.55       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.55         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.55  thf('36', plain,
% 0.21/0.55      (![X26 : $i, X27 : $i]:
% 0.21/0.55         (~ (m1_subset_1 @ X26 @ X27)
% 0.21/0.55          | (r2_hidden @ X26 @ X27)
% 0.21/0.55          | (v1_xboole_0 @ X27))),
% 0.21/0.55      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.55  thf('37', plain,
% 0.21/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.55        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.55  thf(fc1_subset_1, axiom,
% 0.21/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.55  thf('38', plain, (![X31 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.21/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.55  thf('39', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.55      inference('clc', [status(thm)], ['37', '38'])).
% 0.21/0.55  thf(d1_zfmisc_1, axiom,
% 0.21/0.55    (![A:$i,B:$i]:
% 0.21/0.55     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.21/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.21/0.55  thf('40', plain,
% 0.21/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.55         (~ (r2_hidden @ X24 @ X23)
% 0.21/0.55          | (r1_tarski @ X24 @ X22)
% 0.21/0.55          | ((X23) != (k1_zfmisc_1 @ X22)))),
% 0.21/0.55      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.21/0.55  thf('41', plain,
% 0.21/0.55      (![X22 : $i, X24 : $i]:
% 0.21/0.55         ((r1_tarski @ X24 @ X22) | ~ (r2_hidden @ X24 @ (k1_zfmisc_1 @ X22)))),
% 0.21/0.55      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.55  thf('42', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.21/0.55      inference('sup-', [status(thm)], ['39', '41'])).
% 0.21/0.55  thf('43', plain,
% 0.21/0.55      (((r1_xboole_0 @ sk_B @ sk_C_3)) <= (((r1_xboole_0 @ sk_B @ sk_C_3)))),
% 0.21/0.55      inference('split', [status(esa)], ['22'])).
% 0.21/0.55  thf('44', plain,
% 0.21/0.55      (((r1_xboole_0 @ sk_B @ sk_C_3)) | 
% 0.21/0.55       ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3)))),
% 0.21/0.55      inference('split', [status(esa)], ['22'])).
% 0.21/0.55  thf('45', plain, (((r1_xboole_0 @ sk_B @ sk_C_3))),
% 0.21/0.55      inference('sat_resolution*', [status(thm)], ['2', '32', '44'])).
% 0.21/0.55  thf('46', plain, ((r1_xboole_0 @ sk_B @ sk_C_3)),
% 0.21/0.55      inference('simpl_trail', [status(thm)], ['43', '45'])).
% 0.21/0.55  thf(t86_xboole_1, axiom,
% 0.21/0.55    (![A:$i,B:$i,C:$i]:
% 0.21/0.55     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.55       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 0.21/0.55  thf('47', plain,
% 0.21/0.55      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.55         (~ (r1_tarski @ X16 @ X17)
% 0.21/0.55          | ~ (r1_xboole_0 @ X16 @ X18)
% 0.21/0.55          | (r1_tarski @ X16 @ (k4_xboole_0 @ X17 @ X18)))),
% 0.21/0.55      inference('cnf', [status(esa)], [t86_xboole_1])).
% 0.21/0.55  thf('48', plain,
% 0.21/0.55      (![X0 : $i]:
% 0.21/0.55         ((r1_tarski @ sk_B @ (k4_xboole_0 @ X0 @ sk_C_3))
% 0.21/0.55          | ~ (r1_tarski @ sk_B @ X0))),
% 0.21/0.55      inference('sup-', [status(thm)], ['46', '47'])).
% 0.21/0.55  thf('49', plain, ((r1_tarski @ sk_B @ (k4_xboole_0 @ sk_A @ sk_C_3))),
% 0.21/0.55      inference('sup-', [status(thm)], ['42', '48'])).
% 0.21/0.55  thf('50', plain,
% 0.21/0.55      (((k3_subset_1 @ sk_A @ sk_C_3) = (k4_xboole_0 @ sk_A @ sk_C_3))),
% 0.21/0.55      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.55  thf('51', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C_3))),
% 0.21/0.55      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.55  thf('52', plain, ($false), inference('demod', [status(thm)], ['34', '51'])).
% 0.21/0.55  
% 0.21/0.55  % SZS output end Refutation
% 0.21/0.55  
% 0.21/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
